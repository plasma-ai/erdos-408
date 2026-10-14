import Erdos821.Blueprint.Graph
import Mathlib.Data.Int.CardIntervalMod

noncomputable section
open scoped BigOperators
open Filter
open Erdos821.Blueprint.Graph
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Core

lemma exp_nat_pow_eq (y : ℝ) (n : ℕ) :
    Real.exp y ^ n = Real.exp ((n : ℝ) * y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Real.exp_add]

lemma one_half_pow_eq_exp (n : ℕ) :
    (1 / 2 : ℝ) ^ n = Real.exp (-(n : ℝ) * Real.log 2) := by
  have hhalf : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2) ^ n := by rw [hhalf]
    _ = Real.exp ((n : ℝ) * (-Real.log 2)) := exp_nat_pow_eq (-Real.log 2) n
    _ = Real.exp (-(n : ℝ) * Real.log 2) := by congr 1 <;> ring

lemma stirlingSeq_lower_one (n : ℕ) : 1 ≤ Stirling.stirlingSeq (n + 1) := by
  have hlog := Stirling.log_stirlingSeq_bounded_by_constant n
  have hconst : 0 < 1 - (1 : ℝ) / 12 - Real.log 2 / 2 := by
    have hlog2 : Real.log 2 < 1 := by
      have hh := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≠ 1 by norm_num)
      norm_num at hh ⊢
      linarith
    nlinarith
  have hlog' : 0 ≤ Real.log (Stirling.stirlingSeq (n + 1)) := by linarith
  have hpos := Stirling.stirlingSeq'_pos n
  have hexp := Real.exp_le_exp.mpr hlog'
  simpa [Real.exp_log hpos] using hexp

lemma factorial_ge_rpow_div_exp (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hncast : (0 : ℝ) < n := by exact_mod_cast hn
  have hnge : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hseq : 1 ≤ Stirling.stirlingSeq n := by
    have hseq0 := stirlingSeq_lower_one (n - 1)
    have hsub : n - 1 + 1 = n := by omega
    rw [hsub] at hseq0
    exact hseq0
  unfold Stirling.stirlingSeq at hseq
  have hden : 0 < Real.sqrt (2 * (n : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hfac := (le_div_iff₀ hden).mp hseq
  have hroot : 1 ≤ Real.sqrt (2 * (n : ℝ)) := by
    apply Real.one_le_sqrt.mpr
    nlinarith
  have hfac' : Real.sqrt (2 * (n : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    simpa using hfac
  have hpow0 : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  calc
    ((n : ℝ) / Real.exp 1) ^ n = 1 * ((n : ℝ) / Real.exp 1) ^ n := by ring
    _ ≤ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n :=
      mul_le_mul_of_nonneg_right hroot hpow0
    _ ≤ (n.factorial : ℝ) := hfac'

lemma factorial_tail_small_of_linear_degree {lambdaTot : ℝ} (hlambda : 0 ≤ lambdaTot)
    (n : ℕ) (hn : 0 < n)
    (hratio : Real.exp 1 * lambdaTot / (n : ℝ) ≤ 1 / 2) :
    lambdaTot ^ n / (n.factorial : ℝ) ≤ (1 / 2) ^ n := by
  have hfac := factorial_ge_rpow_div_exp n hn
  have hden : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hnum : 0 ≤ lambdaTot ^ n := by positivity
  have hncast : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  calc
    lambdaTot ^ n / (n.factorial : ℝ) ≤
        lambdaTot ^ n / ((n : ℝ) / Real.exp 1) ^ n :=
      div_le_div_of_nonneg_left hnum hden hfac
    _ = (Real.exp 1 * lambdaTot / (n : ℝ)) ^ n := by
      calc
        lambdaTot ^ n / ((n : ℝ) / Real.exp 1) ^ n =
            lambdaTot ^ n / ((n : ℝ) ^ n / (Real.exp 1) ^ n) := by rw [div_pow]
        _ = ((Real.exp 1) ^ n * lambdaTot ^ n) / (n : ℝ) ^ n := by
              field_simp [hncast, he]
        _ = (Real.exp 1 * lambdaTot) ^ n / (n : ℝ) ^ n := by rw [← mul_pow]
        _ = (Real.exp 1 * lambdaTot / (n : ℝ)) ^ n := by rw [div_pow]
    _ ≤ (1 / 2) ^ n := by gcongr

lemma card_biUnion_le_sum_card {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) :
    (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Finset.card_union_le (t a) (s.biUnion t)).trans
        (Nat.add_le_add_left ih _)

lemma groupPrime_upper_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (hL : 1 ≤ L x) (p : P.GroupPrime) :
    (p.val : ℝ) ≤ Real.exp ((L x) ^ F.d) := by
  have hmem : p.val ∈ Finset.univ.biUnion P.primes := by
    simpa [PrimeGroups.allPrimes] using p.property
  rcases Finset.mem_biUnion.mp hmem with ⟨g, hg, hpg⟩
  rcases hP with ⟨_, _, _, _, _, hprime⟩
  have hp := hprime g p.val hpg
  cases hb : P.big g with
  | true =>
      simp [hb] at hp
      exact hp.2
  | false =>
      simp [hb] at hp
      have hbd : F.b ≤ F.d := le_of_lt (lt_trans F.bc F.cd)
      have hpow : (L x) ^ F.b ≤ (L x) ^ F.d :=
        Real.rpow_le_rpow_of_exponent_le hL hbd
      exact hp.2.trans (Real.exp_le_exp.mpr hpow)

lemma visitQ_bounds {F : FixedData} (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ visitQ F.q n i ∧ visitQ F.q n i ≤ 1 := by
  unfold visitQ
  by_cases hi : i.val = 0 ∨ i.val = n
  · rw [if_pos hi]
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr F.q_lt.le⟩
  · rw [if_neg hi]
    exact ⟨F.q_pos.le, F.q_lt.le⟩

lemma group_count_le_two_C0_mul_T {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) :
    (P.count : ℝ) ≤ 2 * F.C₀ * T x := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset P.Group)) (p := fun g => P.big g = false)
  have hgroups : P.smallGroups.card + P.bigGroups.card = P.count := by
    simpa [PrimeGroups.smallGroups, PrimeGroups.bigGroups] using hcard
  rcases hP with ⟨_, hsmall, _, hbig, _⟩
  have hgroupsR : (P.smallGroups.card : ℝ) + (P.bigGroups.card : ℝ) = P.count := by
    exact_mod_cast hgroups
  calc
    (P.count : ℝ) = (P.smallGroups.card : ℝ) + (P.bigGroups.card : ℝ) := hgroupsR.symm
    _ ≤ F.C₀ * T x + F.C₀ * T x := add_le_add hsmall hbig
    _ = 2 * F.C₀ * T x := by ring

lemma allPrimes_sum_le_exp_bound {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (hL : 1 ≤ L x) :
    (∑ p ∈ P.allPrimes, (p : ℝ)) ≤
      3 * (P.count : ℝ) * Real.exp (2 * (L x) ^ F.d) := by
  classical
  let M : ℝ := Real.exp ((L x) ^ F.d)
  have hMpos : 0 < M := Real.exp_pos _
  have hMge1 : 1 ≤ M := by
    apply Real.one_le_exp_iff.mpr
    positivity
  have hceil : (Nat.ceil M : ℝ) < M + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset P.Group)) P.primes := by
    intro g hg k hk hne
    exact P.disjoint g k hne
  have hsumParts :
      (∑ p ∈ P.allPrimes, (p : ℝ)) =
        ∑ g : P.Group, ∑ p ∈ P.primes g, (p : ℝ) := by
    simpa [PrimeGroups.allPrimes] using
      (Finset.sum_biUnion hdisj (f := fun p : ℕ => (p : ℝ)))
  have hgroup : ∀ g : P.Group,
      (∑ p ∈ P.primes g, (p : ℝ)) ≤ 3 * M ^ 2 := by
    intro g
    have hsubset : P.primes g ⊆ Finset.Iic (Nat.ceil M) := by
      intro p hp
      have hpM := groupPrime_upper_of_admissible hP hL
        (⟨p, Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hp⟩⟩ : P.GroupPrime)
      have hpnat : p ≤ Nat.ceil M := by
        have hreal : (p : ℝ) ≤ (Nat.ceil M : ℝ) := by
          dsimp [M] at hpM ⊢
          exact hpM.trans (Nat.le_ceil _)
        exact_mod_cast hreal
      exact Finset.mem_Iic.mpr hpnat
    have hcard : (P.primes g).card ≤ Nat.ceil M + 1 := by
      calc
        (P.primes g).card ≤ (Finset.Iic (Nat.ceil M)).card := Finset.card_le_card hsubset
        _ = Nat.ceil M + 1 := by simp
    calc
      (∑ p ∈ P.primes g, (p : ℝ)) ≤
          ∑ p ∈ P.primes g, M := by
            apply Finset.sum_le_sum
            intro p hp
            have hpM := groupPrime_upper_of_admissible hP hL
              (⟨p, Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hp⟩⟩ : P.GroupPrime)
            simpa [M] using hpM
      _ = (P.primes g).card * M := by simp [mul_comm]
      _ ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) * M := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hMpos.le
      _ ≤ 3 * M ^ 2 := by
            have hcardR : ((Nat.ceil M + 1 : ℕ) : ℝ) ≤ M + 2 := by
              push_cast
              linarith [hceil]
            nlinarith [hMge1]
  calc
    (∑ p ∈ P.allPrimes, (p : ℝ)) =
        ∑ g : P.Group, ∑ p ∈ P.primes g, (p : ℝ) := hsumParts
    _ ≤ ∑ _g : P.Group, 3 * M ^ 2 := Finset.sum_le_sum fun g hg => hgroup g
    _ = 3 * (P.count : ℝ) * (Real.exp ((L x) ^ F.d) * Real.exp ((L x) ^ F.d)) := by
          simp [M]
          ring
    _ = 3 * (P.count : ℝ) * Real.exp ((L x) ^ F.d + (L x) ^ F.d) := by
          rw [← Real.exp_add]
    _ = 3 * (P.count : ℝ) * Real.exp (2 * (L x) ^ F.d) := by
          congr 2 <;> ring

lemma groupPrime_sum_eq_allPrimes {P : PrimeGroups} (f : ℕ → ℝ) :
    (∑ p : P.GroupPrime, f p.val) = ∑ p ∈ P.allPrimes, f p := by
  classical
  change (∑ p ∈ P.allPrimes.attach, f p.val) = _
  rw [Finset.sum_attach]

lemma tendsto_T_div_L_rpow (r : ℝ) (hr : 0 < r) :
    Tendsto (fun x : ℝ => T x / (L x) ^ r) atTop (nhds 0) := by
  have hL : Tendsto L atTop atTop := by
    change Tendsto Real.log atTop atTop
    exact Real.tendsto_log_atTop
  have hratio : Tendsto (fun y : ℝ => Real.log y / y ^ r) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  simpa [T, L, Function.comp_def] using hratio.comp hL

lemma tendsto_T_sq_div_L_rpow (r : ℝ) (hr : 0 < r) :
    Tendsto (fun x : ℝ => (T x) ^ 2 / (L x) ^ r) atTop (nhds 0) := by
  have hL : Tendsto L atTop atTop := by
    change Tendsto Real.log atTop atTop
    exact Real.tendsto_log_atTop
  have hratio : Tendsto (fun y : ℝ => (Real.log y) ^ (2 : ℝ) / y ^ r)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop 2 hr).tendsto_div_nhds_zero
  simpa [T, L, Function.comp_def, Real.rpow_natCast] using hratio.comp hL

lemma eventually_T_sq_le_L_rpow (r : ℝ) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, (T x) ^ 2 ≤ (L x) ^ r := by
  have hlim := tendsto_T_sq_div_L_rpow r hr
  have hsmall : ∀ᶠ x : ℝ in atTop,
      (T x) ^ 2 / (L x) ^ r < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  have hL : Tendsto L atTop atTop := by
    change Tendsto Real.log atTop atTop
    exact Real.tendsto_log_atTop
  filter_upwards [hsmall, hL.eventually_gt_atTop 0] with x hx hLx
  have hden : 0 < (L x) ^ r := by positivity
  have hlt := (div_lt_iff₀ hden).mp hx
  exact le_of_lt (by simpa using hlt)

lemma eventually_const_mul_L_le_exp_Lpow (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, c * L x ≤ Real.exp ((L x) ^ d) := by
  have hL : Tendsto L atTop atTop := by
    change Tendsto Real.log atTop atTop
    exact Real.tendsto_log_atTop
  have hpow : Tendsto (fun x : ℝ => (L x) ^ d) atTop atTop :=
    (tendsto_rpow_atTop hd).comp hL
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d⁻¹ 1 (by norm_num)).comp hpow
  have hsmall : ∀ᶠ x : ℝ in atTop,
      c * (((L x) ^ d) ^ d⁻¹ * Real.exp (-((L x) ^ d))) < 1 := by
    have hcT : Tendsto (fun x : ℝ =>
        c * ((L x) ^ d) ^ d⁻¹ * Real.exp (-((L x) ^ d))) atTop (nhds 0) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hdecay)
    simpa [mul_assoc] using
      hcT.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, hL.eventually_ge_atTop 1] with x hx hLx
  have hpowEq : ((L x) ^ d) ^ d⁻¹ = L x :=
    Real.rpow_rpow_inv (le_trans (by norm_num) hLx) hd.ne'
  have hsmall' : c * L x * Real.exp (-((L x) ^ d)) < 1 := by
    simpa [hpowEq, mul_assoc] using hx
  have hdiv : c * L x / Real.exp ((L x) ^ d) < 1 := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    simpa [mul_assoc] using hsmall'
  exact (div_lt_one (Real.exp_pos _)).mp hdiv |>.le

lemma eventually_const_mul_L_rpow_le_exp_L_rpow
    (c s d : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, c * (L x) ^ s ≤ Real.exp ((L x) ^ d) := by
  have hL : Tendsto L atTop atTop := by
    change Tendsto Real.log atTop atTop
    exact Real.tendsto_log_atTop
  have hpow : Tendsto (fun x : ℝ => (L x) ^ d) atTop atTop :=
    (tendsto_rpow_atTop hd).comp hL
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / d) 1 (by norm_num)).comp hpow
  have hsmall : ∀ᶠ x : ℝ in atTop,
      c * (((L x) ^ d) ^ (s / d) * Real.exp (-((L x) ^ d))) < 1 := by
    have hcT : Tendsto (fun x : ℝ =>
        c * ((L x) ^ d) ^ (s / d) * Real.exp (-((L x) ^ d))) atTop (nhds 0) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hdecay)
    simpa [mul_assoc] using
      hcT.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, hL.eventually_gt_atTop 0] with x hx hLx
  have hpowEq : ((L x) ^ d) ^ (s / d) = (L x) ^ s := by
    rw [← Real.rpow_mul (le_of_lt hLx) d (s / d)]
    congr 1
    field_simp [hd.ne']
  have hsmall' : c * (L x) ^ s * Real.exp (-((L x) ^ d)) < 1 := by
    simpa [hpowEq, mul_assoc] using hx
  have hdiv : c * (L x) ^ s / Real.exp ((L x) ^ d) < 1 := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    simpa [mul_assoc] using hsmall'
  exact (div_lt_one (Real.exp_pos _)).mp hdiv |>.le

lemma L_rpow_052_mul_rpow_div_eq_inv {x d : ℝ} (hL : 1 ≤ L x) :
    (L x) ^ ((52 : ℝ) / 100) * (L x) ^ d / L x =
      ((L x) ^ ((48 : ℝ) / 100 - d))⁻¹ := by
  have hLpos : 0 < L x := by linarith
  calc
    (L x) ^ ((52 : ℝ) / 100) * (L x) ^ d / L x =
        (L x) ^ (((52 : ℝ) / 100) + d) / L x := by
          rw [← Real.rpow_add hLpos]
    _ = (L x) ^ (((52 : ℝ) / 100 + d) - 1) := by
          simpa [Real.rpow_one] using
            (Real.rpow_sub hLpos (((52 : ℝ) / 100) + d) 1).symm
    _ = (L x) ^ (-( ((48 : ℝ) / 100 - d))) := by congr 1 <;> ring
    _ = ((L x) ^ ((48 : ℝ) / 100 - d))⁻¹ := by
          rw [Real.rpow_neg hLpos.le]

lemma dyad_card_real_lower_of_two_le {X : ℝ} (hX : 2 ≤ X) :
    X / 2 ≤ ((dyad X).card : ℝ) := by
  have hlohi : (⌈X⌉ : ℤ) ≤ ⌈2 * X⌉ := Int.ceil_le_ceil (by linarith)
  have hcard : ((dyad X).card : ℝ) = (⌈2 * X⌉ : ℝ) - (⌈X⌉ : ℝ) := by
    dsimp [dyad]
    exact_mod_cast Int.card_Ico_of_le (⌈X⌉ : ℤ) ⌈2 * X⌉ hlohi
  have hhi : 2 * X ≤ (⌈2 * X⌉ : ℝ) := by exact_mod_cast (Int.le_ceil (2 * X))
  have hlo : (⌈X⌉ : ℝ) < X + 1 := by exact_mod_cast (Int.ceil_lt_add_one X)
  rw [hcard]
  linarith

lemma dyad_card_inv_le_exp_of_scale {x gamma X : ℝ} (hx : 0 < x)
    (hXpow : x ^ gamma ≤ X) (hXtwo : 2 ≤ X) :
    ((dyad X).card : ℝ)⁻¹ ≤ 2 * Real.exp (-gamma * L x) := by
  have hlen := dyad_card_real_lower_of_two_le hXtwo
  have hxpow : x ^ gamma = Real.exp (gamma * L x) :=
    by simpa [L, mul_comm] using (Real.rpow_def_of_pos hx gamma)
  have hbase : Real.exp (gamma * L x) / 2 ≤ (dyad X).card := by
    calc
      Real.exp (gamma * L x) / 2 = x ^ gamma / 2 := by rw [← hxpow]
      _ ≤ X / 2 := div_le_div_of_nonneg_right hXpow (by norm_num)
      _ ≤ (dyad X).card := hlen
  have hden : 0 < Real.exp (gamma * L x) / 2 := by positivity
  have hcard : 0 < ((dyad X).card : ℝ) := lt_of_lt_of_le hden hbase
  calc
    ((dyad X).card : ℝ)⁻¹ ≤ (Real.exp (gamma * L x) / 2)⁻¹ := by
      exact (inv_le_inv₀ hcard hden).2 hbase
    _ = 2 * Real.exp (-gamma * L x) := by
      calc
        (Real.exp (gamma * L x) / 2)⁻¹ = 2 / Real.exp (gamma * L x) := by
          rw [inv_div]
        _ = 2 * Real.exp (-gamma * L x) := by
          rw [div_eq_mul_inv, ← Real.exp_neg]
          ring

lemma interval_modEq_count_error (a b r v : ℤ) (hr : 0 < r) (hab : a ≤ b) :
    abs ((({z ∈ Finset.Ico a b | z ≡ v [ZMOD r]}.card : ℝ)) -
      (Finset.Ico a b).card / (r : ℝ)) ≤ 1 := by
  let ya : ℚ := ((a - v : ℤ) : ℚ) / r
  let yb : ℚ := ((b - v : ℤ) : ℚ) / r
  have hy : ya ≤ yb := by
    dsimp [ya, yb]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (sub_le_sub_right hab v)
    · exact_mod_cast hr.le
  have hceil : ⌈ya⌉ ≤ ⌈yb⌉ := Int.ceil_le_ceil hy
  have hcount :
      (({z ∈ Finset.Ico a b | z ≡ v [ZMOD r]}.card : ℤ)) = ⌈yb⌉ - ⌈ya⌉ := by
    have hc := Int.Ico_filter_modEq_card a b hr v
    have hc' :
        (({z ∈ Finset.Ico a b | z ≡ v [ZMOD r]}.card : ℤ)) =
          max (⌈yb⌉ - ⌈ya⌉) 0 := by
      simpa only [ya, yb, Int.cast_sub] using hc
    rw [max_eq_left (sub_nonneg.mpr hceil)] at hc'
    exact hc'
  have hcard : ((Finset.Ico a b).card : ℝ) = (b : ℝ) - a := by
    exact_mod_cast Int.card_Ico_of_le a b hab
  have hcountR :
      (({z ∈ Finset.Ico a b | z ≡ v [ZMOD r]}.card : ℝ)) =
        (⌈yb⌉ : ℝ) - ⌈ya⌉ := by
    exact_mod_cast hcount
  have hya : (ya : ℝ) ≤ (⌈ya⌉ : ℝ) := by
    exact_mod_cast Int.le_ceil ya
  have hyb : (yb : ℝ) ≤ (⌈yb⌉ : ℝ) := by
    exact_mod_cast Int.le_ceil yb
  have hya' : (⌈ya⌉ : ℝ) < ya + 1 := by
    exact_mod_cast Int.ceil_lt_add_one ya
  have hyb' : (⌈yb⌉ : ℝ) < yb + 1 := by
    exact_mod_cast Int.ceil_lt_add_one yb
  have hyaR : (ya : ℝ) = ((a : ℝ) - v) / r := by
    dsimp [ya]
    push_cast
    ring
  have hybR : (yb : ℝ) = ((b : ℝ) - v) / r := by
    dsimp [yb]
    push_cast
    ring
  have hratio : (Finset.Ico a b).card / (r : ℝ) = (yb : ℝ) - ya := by
    rw [hcard, hyaR, hybR]
    ring
  rw [hcountR, hratio]
  rw [abs_le]
  constructor <;> linarith

lemma crt_fiber_card_one {ι : Type*} [Fintype ι] (m : ι → ℕ)
    [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (Function.onFun Nat.Coprime m)) (y : Π i, ZMod (m i)) :
    Fintype.card {z : ZMod (∏ i, m i) // ZMod.prodEquivPi m hc z = y} = 1 := by
  classical
  let e := ZMod.prodEquivPi m hc
  let E : {z : ZMod (∏ i, m i) // e z = y} ≃ PUnit.{1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨e.symm y, e.apply_symm_apply y⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply e.injective
        exact (z.2.trans (e.apply_symm_apply y).symm).symm
      right_inv := by
        intro u
        cases u
        rfl }
  simpa using Fintype.card_congr E

lemma interval_crt_modEq_count_error {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 0 < m i)
    (hc : Pairwise (Function.onFun Nat.Coprime (fun i : {i // i ∈ s} => m i.1)))
    (r : (i : {i // i ∈ s}) → ZMod (m i.1))
    (a b : ℤ) (hab : a ≤ b) :
    abs ((({z ∈ Finset.Ico a b | ∀ i : {i // i ∈ s},
        (z : ZMod (m i.1)) = r i}.card : ℝ)) -
      (Finset.Ico a b).card /
        (∏ i : {i // i ∈ s}, m i.1 : ℝ)) ≤ 1 := by
  classical
  let Q : ℕ := ∏ i : {i // i ∈ s}, m i.1
  let e := ZMod.prodEquivPi (fun i : {i // i ∈ s} => m i.1) hc
  let y : (i : {i // i ∈ s}) → ZMod (m i.1) := r
  let c : ZMod Q := e.symm y
  let v : ℤ := c.val
  have hQ : 0 < Q := by
    dsimp [Q]
    apply Finset.prod_pos
    intro i hi
    exact hm i.1 i.2
  haveI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hcval : (v : ZMod Q) = c := by
    dsimp [v]
    norm_cast
    exact ZMod.natCast_zmod_val c
  have happly : ∀ z : ℤ, ∀ i : {i // i ∈ s},
      e (z : ZMod Q) i = (z : ZMod (m i.1)) := by
    intro z i
    have he := map_intCast e z
    exact congrFun he i
  have hcoord (z : ℤ) :
      (e (z : ZMod Q) = y) ↔ ∀ i : {i // i ∈ s},
        (z : ZMod (m i.1)) = r i := by
    constructor
    · intro hz i
      have hi := congrFun hz i
      rw [happly z i] at hi
      simpa [y] using hi
    · intro hz
      funext i
      rw [happly z i]
      simpa [y] using hz i
  have hclass (z : ℤ) :
      (e (z : ZMod Q) = y) ↔ z ≡ v [ZMOD (Q : ℤ)] := by
    have hEq : (e (z : ZMod Q) = y) ↔ (z : ZMod Q) = c := by
      constructor
      · intro hz
        apply e.injective
        exact hz.trans (e.apply_symm_apply y).symm
      · intro hz
        rw [hz]
        exact e.apply_symm_apply y
    rw [hEq, ← hcval]
    exact ZMod.intCast_eq_intCast_iff z v Q
  have hfilter :
      {z ∈ Finset.Ico a b | ∀ i : {i // i ∈ s},
        (z : ZMod (m i.1)) = r i} =
      {z ∈ Finset.Ico a b | z ≡ v [ZMOD (Q : ℤ)]} := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hres⟩
      exact ⟨hz, (hclass z).1 ((hcoord z).2 hres)⟩
    · rintro ⟨hz, hres⟩
      exact ⟨hz, (hcoord z).1 ((hclass z).2 hres)⟩
  rw [hfilter]
  have hr : 0 < (Q : ℤ) := by exact_mod_cast hQ
  simpa [Q] using interval_modEq_count_error a b (Q : ℤ) v hr hab

section ElementarySymmetricLemmas

variable {ι : Type*}

def elementarySymmetric (x : ι → ℝ) (s : Finset ι) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i

lemma elementarySymmetric_nonneg [DecidableEq ι] (x : ι → ℝ) (s : Finset ι)
    (k : ℕ) (hx : ∀ i ∈ s, 0 ≤ x i) : 0 ≤ elementarySymmetric x s k := by
  classical
  unfold elementarySymmetric
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro i hi
  exact hx i ((Finset.mem_powersetCard.mp ht).1 hi)

lemma elementarySymmetric_insert [DecidableEq ι] (x : ι → ℝ) (s : Finset ι)
    (a : ι) (ha : a ∉ s) (k : ℕ) :
    elementarySymmetric x (insert a s) (k + 1) =
      elementarySymmetric x s (k + 1) + x a * elementarySymmetric x s k := by
  classical
  rw [elementarySymmetric, Finset.powersetCard_succ_insert ha k]
  have hd : Disjoint (Finset.powersetCard (k + 1) s)
      ((Finset.powersetCard k s).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht'
    have hau : a ∈ insert a u := by simp
    exact ha ((Finset.mem_powersetCard.mp ht).1 hau)
  rw [Finset.sum_union hd]
  rw [Finset.sum_image]
  · simp only [elementarySymmetric]
    have hinner :
        (∑ t ∈ Finset.powersetCard k s, ∏ i ∈ insert a t, x i) =
          x a * (∑ t ∈ Finset.powersetCard k s, ∏ i ∈ t, x i) := by
      calc
        (∑ t ∈ Finset.powersetCard k s, ∏ i ∈ insert a t, x i) =
            ∑ t ∈ Finset.powersetCard k s, x a * (∏ i ∈ t, x i) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hat : a ∉ t := Finset.notMem_mono (Finset.mem_powersetCard.mp ht).1 ha
          rw [Finset.prod_insert hat]
        _ = x a * (∑ t ∈ Finset.powersetCard k s, ∏ i ∈ t, x i) := by
          rw [Finset.mul_sum]
    rw [hinner]
  · intro t ht u hu htu
    have hts := (Finset.mem_powersetCard.mp ht).1
    have hus := (Finset.mem_powersetCard.mp hu).1
    have hat : a ∉ t := fun h => ha (hts h)
    have hau : a ∉ u := fun h => ha (hus h)
    apply Finset.ext
    intro z
    have hzmem : z ∈ insert a t ↔ z ∈ insert a u :=
      eq_iff_iff.mp (congrArg (fun w : Finset ι => z ∈ w) htu)
    by_cases hza : z = a
    · subst z
      simp [hat, hau]
    · simpa [hza] using hzmem

def inclusionTruncation (x : ι → ℝ) (s : Finset ι) (h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (h + 1), (-1 : ℝ) ^ k * elementarySymmetric x s k

lemma elementarySymmetric_zero (x : ι → ℝ) (s : Finset ι) :
    elementarySymmetric x s 0 = 1 := by
  simp [elementarySymmetric]

lemma elementarySymmetric_empty (x : ι → ℝ) (k : ℕ) :
    elementarySymmetric x ∅ k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [elementarySymmetric]
  · have hcard : (∅ : Finset ι).card < k := by simp; omega
    unfold elementarySymmetric
    rw [Finset.powersetCard_eq_empty.mpr hcard]
    simp [hk]

lemma inclusionTruncation_zero (x : ι → ℝ) (s : Finset ι) :
    inclusionTruncation x s 0 = 1 := by
  simp [inclusionTruncation, elementarySymmetric_zero]

lemma inclusionTruncation_succ (x : ι → ℝ) (s : Finset ι) (h : ℕ) :
    inclusionTruncation x s (h + 1) =
      inclusionTruncation x s h + (-1 : ℝ) ^ (h + 1) * elementarySymmetric x s (h + 1) := by
  simp [inclusionTruncation, Finset.sum_range_succ]

lemma inclusionTruncation_insert [DecidableEq ι] (x : ι → ℝ) (s : Finset ι)
    (a : ι) (ha : a ∉ s) (h : ℕ) :
    inclusionTruncation x (insert a s) (h + 1) =
      inclusionTruncation x s (h + 1) - x a * inclusionTruncation x s h := by
  induction h with
  | zero =>
      simp only [inclusionTruncation_succ, inclusionTruncation_zero,
        elementarySymmetric_insert x s a ha 0, elementarySymmetric_zero]
      ring
  | succ h ih =>
      rw [inclusionTruncation_succ x (insert a s) (h + 1), ih,
        elementarySymmetric_insert x s a ha (h + 1),
        inclusionTruncation_succ x s (h + 1), inclusionTruncation_succ x s h]
      simp only [pow_succ]
      ring

lemma inclusionTruncation_bonferroni [DecidableEq ι] (x : ι → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) → ∀ h : ℕ,
      (h % 2 = 0 → ∏ i ∈ s, (1 - x i) ≤ inclusionTruncation x s h) ∧
      (h % 2 = 1 → inclusionTruncation x s h ≤ ∏ i ∈ s, (1 - x i)) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro hx h
      constructor
      · intro _
        simp [inclusionTruncation, elementarySymmetric_empty]
      · intro _
        simp [inclusionTruncation, elementarySymmetric_empty]
  | @insert a s ha ih =>
      intro hx h
      have hxs : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := by
        intro i hi
        exact hx i (Finset.mem_insert_of_mem hi)
      have hxa := hx a (Finset.mem_insert_self a s)
      have ihall := ih hxs
      constructor
      · intro heven
        by_cases hzero : h = 0
        · subst h
          rw [inclusionTruncation_zero]
          simpa using (Finset.prod_le_one₀ (s := insert a s) (f := fun i => 1 - x i)
            (fun i hi => sub_nonneg.mpr (hx i hi).2)
            (fun i hi => by linarith [(hx i hi).1]))
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
          have heven' : (k + 1) % 2 = 0 := by simpa using heven
          have hodd : k % 2 = 1 := by omega
          have hup := (ihall (k + 1)).1 heven'
          have hlo := (ihall k).2 hodd
          rw [inclusionTruncation_insert x s a ha k, Finset.prod_insert ha]
          nlinarith [mul_nonneg hxa.1 (sub_nonneg.mpr hlo)]
      · intro hodd
        have hzero : h ≠ 0 := by
          intro hh
          simp [hh] at hodd
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        have heven' : k % 2 = 0 := by omega
        have hodd' : (k + 1) % 2 = 1 := by simpa using hodd
        have hup := (ihall k).1 heven'
        have hlo := (ihall (k + 1)).2 hodd'
        rw [inclusionTruncation_insert x s a ha k, Finset.prod_insert ha]
        nlinarith [mul_nonneg hxa.1 (sub_nonneg.mpr hup)]

lemma pow_add_linear_lower (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    u ^ (n + 1) + (n + 1 : ℝ) * v * u ^ n ≤ (u + v) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmul := mul_le_mul_of_nonneg_right ih (add_nonneg hu hv)
      calc
        u ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * v * u ^ (n + 1) ≤
            u ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * v * u ^ (n + 1) +
              (n + 1 : ℝ) * v ^ 2 * u ^ n := by
          have hnonneg : 0 ≤ (n + 1 : ℝ) * v ^ 2 * u ^ n := by positivity
          linarith
        _ = (u ^ (n + 1) + (n + 1 : ℝ) * v * u ^ n) * (u + v) := by
          push_cast
          ring
        _ ≤ (u + v) ^ (n + 1) * (u + v) := hmul
        _ = (u + v) ^ (n + 1 + 1) := by rw [pow_succ]; ring

lemma pow_add_factorial_bound (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    u ^ (n + 1) / ((n + 1).factorial : ℝ) +
      v * u ^ n / (n.factorial : ℝ) ≤
        (u + v) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hfact0 : 0 < (n.factorial : ℝ) := by positivity
  have hfact1 : 0 < ((n + 1).factorial : ℝ) := by positivity
  have hf : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
    simp [Nat.factorial_succ]
  have hterm : v * u ^ n / (n.factorial : ℝ) =
      ((n + 1 : ℝ) * v * u ^ n) / ((n + 1).factorial : ℝ) := by
    rw [hf]
    field_simp
  rw [hterm, ← add_div]
  apply (div_le_div_iff₀ hfact1 hfact1).2
  have hpow := pow_add_linear_lower u v hu hv n
  have hmul : 0 ≤ ((u + v) ^ (n + 1) -
      (u ^ (n + 1) + (n + 1 : ℝ) * v * u ^ n)) * ((n + 1).factorial : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hpow) hfact1.le
  nlinarith

lemma elementarySymmetric_bound [DecidableEq ι] (x : ι → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ x i) → ∀ k : ℕ,
      elementarySymmetric x s k ≤ (∑ i ∈ s, x i) ^ k / (k.factorial : ℝ) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro hx k
      cases k with
      | zero => simp [elementarySymmetric]
      | succ k => simp [elementarySymmetric_empty]
  | @insert a s ha ih =>
      intro hx k
      have hxs : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx i (Finset.mem_insert_of_mem hi)
      have hxa := hx a (Finset.mem_insert_self a s)
      cases k with
      | zero => simp [elementarySymmetric]
      | succ k =>
          have hsum : (∑ i ∈ insert a s, x i) = (∑ i ∈ s, x i) + x a := by
            rw [Finset.sum_insert ha]
            ring
          calc
            elementarySymmetric x (insert a s) (k + 1) =
                elementarySymmetric x s (k + 1) + x a * elementarySymmetric x s k :=
              elementarySymmetric_insert x s a ha k
            _ ≤ (∑ i ∈ s, x i) ^ (k + 1) / ((k + 1).factorial : ℝ) +
                x a * ((∑ i ∈ s, x i) ^ k / (k.factorial : ℝ)) := by
              exact add_le_add (ih hxs (k + 1))
                (mul_le_mul_of_nonneg_left (ih hxs k) hxa)
            _ ≤ (∑ i ∈ s, x i + x a) ^ (k + 1) / ((k + 1).factorial : ℝ) :=
              by
                simpa [mul_div_assoc] using
                  (pow_add_factorial_bound (∑ i ∈ s, x i) (x a)
                    (Finset.sum_nonneg hxs) hxa k)
            _ = (∑ i ∈ insert a s, x i) ^ (k + 1) /
                ((k + 1).factorial : ℝ) := by rw [hsum]

end ElementarySymmetricLemmas

lemma elementarySymmetric_two_range_sum_bound {P : PrimeGroups}
    (U : Finset P.GroupPrime) (y : ℝ) (hy : 0 ≤ y) (H : ℕ)
    (hsigma : (∑ p ∈ U, (p.val : ℝ)) ≤ Real.exp (3 * y)) :
    (∑ k ∈ Finset.range (H + 1),
        elementarySymmetric (fun p => (p.val : ℝ)) U k) +
      ∑ k ∈ Finset.range (H + 2),
        elementarySymmetric (fun p => (p.val : ℝ)) U k ≤
      2 * (H + 2 : ℝ) * Real.exp (((H + 1 : ℕ) : ℝ) * (3 * y)) := by
  classical
  let f : P.GroupPrime → ℝ := fun p => (p.val : ℝ)
  let C : ℝ := Real.exp (((H + 1 : ℕ) : ℝ) * (3 * y))
  have hsum0 : 0 ≤ ∑ p ∈ U, f p :=
    Finset.sum_nonneg fun p hp => by positivity
  have hExp1 : 1 ≤ Real.exp (3 * y) := by
    have hy3 : 0 ≤ 3 * y := by positivity
    calc
      1 ≤ 1 + 3 * y := by linarith
      _ ≤ Real.exp (3 * y) := by simpa [add_comm] using Real.add_one_le_exp (3 * y)
  have hper : ∀ k ≤ H + 1,
      elementarySymmetric f U k ≤ C := by
    intro k hk
    have hbound := elementarySymmetric_bound f U
      (fun p hp => by positivity) k
    have hfact : (1 : ℝ) ≤ (k.factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos k))
    calc
      elementarySymmetric f U k ≤
          (∑ p ∈ U, f p) ^ k / (k.factorial : ℝ) := hbound
      _ ≤ (∑ p ∈ U, f p) ^ k := div_le_self (by positivity) hfact
      _ ≤ (Real.exp (3 * y)) ^ k := by gcongr
      _ ≤ (Real.exp (3 * y)) ^ (H + 1) := by
          have hmono : Monotone fun m : ℕ => (Real.exp (3 * y)) ^ m := by
            apply monotone_nat_of_le_succ
            intro m
            rw [pow_succ]
            calc
              (Real.exp (3 * y)) ^ m = (Real.exp (3 * y)) ^ m * 1 := by ring
              _ ≤ (Real.exp (3 * y)) ^ m * Real.exp (3 * y) :=
                mul_le_mul_of_nonneg_left hExp1 (by positivity)
          exact hmono hk
      _ = C := by
          dsimp [C]
          exact exp_nat_pow_eq (3 * y) (H + 1)
  have hsum1 :
      (∑ k ∈ Finset.range (H + 1), elementarySymmetric f U k) ≤
        (H + 1 : ℝ) * C := by
    calc
      _ ≤ ∑ k ∈ Finset.range (H + 1), C :=
        Finset.sum_le_sum fun k hk => by
          have hk' : k < H + 1 := Finset.mem_range.mp hk
          exact hper k (Nat.le_trans (Nat.le_of_lt_succ hk') (Nat.le_succ H))
      _ = _ := by simp
  have hsum2 :
      (∑ k ∈ Finset.range (H + 2), elementarySymmetric f U k) ≤
        (H + 2 : ℝ) * C := by
    calc
      _ ≤ ∑ k ∈ Finset.range (H + 2), C :=
        Finset.sum_le_sum fun k hk => by
          have hk' : k < (H + 1) + 1 := by
            simpa [Nat.add_assoc] using Finset.mem_range.mp hk
          exact hper k (Nat.le_of_lt_succ hk')
      _ = _ := by simp
  calc
    _ ≤ (H + 1 : ℝ) * C + (H + 2 : ℝ) * C := by
      simpa [f] using add_le_add hsum1 hsum2
    _ = ((H + 1 : ℝ) + (H + 2 : ℝ)) * C := by ring
    _ ≤ 2 * (H + 2 : ℝ) * C := by
      have hC0 : 0 ≤ C := by positivity
      have hnum : (H + 1 : ℝ) + (H + 2 : ℝ) ≤ 2 * (H + 2 : ℝ) := by
        push_cast
        linarith
      exact mul_le_mul_of_nonneg_right hnum hC0

def integerPrimePathFactor (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (p : ℕ) (z : ℤ) : ℝ :=
  ∏ i : Fin (n + 1),
    if p ∈ active i then (if (p : ℤ) ∣ z + h i then 1 else 0)
    else if (p : ℤ) ∣ z + h i then q i else 1

def residuePrimePathFactor {P : PrimeGroups} (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (p : P.GroupPrime) (r : Fin p.val) : ℝ :=
  ∏ i : Fin (n + 1),
    if p.val ∈ active i then
      (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then 1 else 0)
    else if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1

def activePrimeSet (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin (n + 1))).biUnion active

def activeGroupPrimes {P : PrimeGroups} (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) : Finset P.GroupPrime :=
  Finset.univ.filter fun p => p.val ∈ activePrimeSet n active

def inactiveGroupPrimes {P : PrimeGroups} (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) : Finset P.GroupPrime :=
  Finset.univ.filter fun p => p.val ∉ activePrimeSet n active

def activeAllowedResidues {P : PrimeGroups} (n : ℕ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (p : P.GroupPrime) : Finset (Fin p.val) :=
  Finset.univ.filter fun r =>
    ∀ i, p.val ∈ active i → (p.val : ℤ) ∣ (r.val : ℤ) + h i

def residuePathDamping {P : PrimeGroups} (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (p : P.GroupPrime) (r : Fin p.val) : ℝ :=
  ∏ i : Fin (n + 1),
    if p.val ∈ active i then 1
    else if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1

lemma mem_activePrimeSet_iff (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) (p : ℕ) :
    p ∈ activePrimeSet n active ↔ ∃ i, p ∈ active i := by
  simp [activePrimeSet]

lemma residuePrimePathFactor_active_split {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) (r : Fin p.val) :
    residuePrimePathFactor n q h active p r =
      if p.val ∈ activePrimeSet n active then
        if r ∈ activeAllowedResidues n h active p then
          residuePathDamping n q h active p r
        else 0
      else residuePathDamping n q h active p r := by
  classical
  by_cases hp : p.val ∈ activePrimeSet n active
  · by_cases hr : r ∈ activeAllowedResidues n h active p
    · have hhit : ∀ i, p.val ∈ active i →
          (p.val : ℤ) ∣ (r.val : ℤ) + h i := (Finset.mem_filter.mp hr).2
      rw [if_pos hp, if_pos hr]
      unfold residuePrimePathFactor residuePathDamping
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hactive : p.val ∈ active i
      · simp [hactive, hhit i hactive]
      · simp [hactive]
    · have hbad : ∃ i, p.val ∈ active i ∧
          ¬ (p.val : ℤ) ∣ (r.val : ℤ) + h i := by
        by_contra hnone
        apply hr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hactive
        by_contra hdiv
        exact hnone ⟨i, hactive, hdiv⟩
      obtain ⟨i, hi, hdiv⟩ := hbad
      rw [if_pos hp, if_neg hr]
      unfold residuePrimePathFactor
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi, hdiv]
  · have hnone : ∀ i, p.val ∉ active i := by
      intro i hi
      exact hp ((mem_activePrimeSet_iff n active p.val).2 ⟨i, hi⟩)
    rw [if_neg hp]
    unfold residuePrimePathFactor residuePathDamping
    apply Finset.prod_congr rfl
    intro i hi
    simp [hnone i]

lemma residuePrimePathFactor_as_allowed_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) (r : Fin p.val) :
    residuePrimePathFactor n q h active p r =
      ∑ r' ∈ activeAllowedResidues n h active p,
        if r = r' then residuePathDamping n q h active p r' else 0 := by
  classical
  rw [residuePrimePathFactor_active_split]
  by_cases hp : p.val ∈ activePrimeSet n active
  · rw [if_pos hp]
    by_cases hr : r ∈ activeAllowedResidues n h active p
    · rw [if_pos hr]
      rw [Finset.sum_eq_single r]
      · simp
      · intro r' hr' hne
        simp [Ne.symm hne]
      · simp [hr]
    · rw [if_neg hr]
      symm
      apply Finset.sum_eq_zero
      intro r' hr'
      by_cases heq : r = r'
      · subst r'
        exact (hr hr').elim
      · simp [heq]
  · rw [if_neg hp]
    have hnone : ∀ i, p.val ∉ active i := by
      intro i hi
      exact hp ((mem_activePrimeSet_iff n active p.val).2 ⟨i, hi⟩)
    have hall : activeAllowedResidues n h active p = Finset.univ := by
      ext r'
      simp [activeAllowedResidues, hnone]
    rw [hall, Finset.sum_eq_single r]
    · simp
    · intro r' hr' hne
      simp [Ne.symm hne]
    · simp

lemma residuePrimePathExpectationFactor_as_allowed_sum {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) :
    (p.val : ℝ)⁻¹ *
        ∑ r : Fin p.val, residuePrimePathFactor n q h active p r =
      (p.val : ℝ)⁻¹ *
        ∑ r ∈ activeAllowedResidues n h active p, residuePathDamping n q h active p r := by
  congr 1
  simp_rw [residuePrimePathFactor_as_allowed_sum]
  rw [Finset.sum_comm]
  simp

lemma integerPrimePathFactor_modEq {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime)
    (z : ℤ) (r : Fin p.val) (hmod : (p.val : ℤ) ∣ z - (r.val : ℤ)) :
    integerPrimePathFactor n q h active p.val z =
      residuePrimePathFactor n q h active p r := by
  have hdiv (i : Fin (n + 1)) :
      ((p.val : ℤ) ∣ z + h i) ↔
        (p.val : ℤ) ∣ (r.val : ℤ) + h i := by
    constructor
    · intro hz
      have hsub := dvd_sub hz hmod
      convert hsub using 1 <;> ring
    · intro hr
      have hadd := dvd_add hmod hr
      convert hadd using 1 <;> ring
  unfold integerPrimePathFactor residuePrimePathFactor
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hactive : p.val ∈ active i <;> simp [hactive, hdiv i]

lemma pathFactor_as_prime_product {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    P.pathFactor n q h active z =
      ∏ p ∈ P.allPrimes, integerPrimePathFactor n q h active p z := by
  rfl

lemma pathFactor_as_groupPrime_product {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    P.pathFactor n q h active z =
      ∏ p : P.GroupPrime, integerPrimePathFactor n q h active p.val z := by
  classical
  calc
    P.pathFactor n q h active z =
        ∏ p ∈ P.allPrimes, integerPrimePathFactor n q h active p z :=
      pathFactor_as_prime_product n q h active z
    _ = ∏ p ∈ P.allPrimes.attach, integerPrimePathFactor n q h active p.val z :=
      (Finset.prod_attach P.allPrimes (fun p => integerPrimePathFactor n q h active p z)).symm
    _ = ∏ p : P.GroupPrime, integerPrimePathFactor n q h active p.val z := by
      simp [PrimeGroups.GroupPrime]

lemma pathFactor_active_inactive_product {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    P.pathFactor n q h active z =
      (∏ p ∈ activeGroupPrimes (P := P) n active,
        integerPrimePathFactor n q h active p.val z) *
      ∏ p ∈ inactiveGroupPrimes (P := P) n active,
        integerPrimePathFactor n q h active p.val z := by
  classical
  rw [pathFactor_as_groupPrime_product]
  rw [← Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset P.GroupPrime))
      (p := fun p => p.val ∈ activePrimeSet n active)
      (f := fun p => integerPrimePathFactor n q h active p.val z)]
  rfl

lemma residuePathFactor_as_prime_product {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (y : P.Residues) :
    P.residuePathFactor n q h active y =
      ∏ p : P.GroupPrime, residuePrimePathFactor n q h active p (y p) := by
  rfl

lemma residueExpectation_factorization {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) :
    P.residueExpectation n q h active =
      ∏ p : P.GroupPrime,
        ((p.val : ℝ)⁻¹ * ∑ r : Fin p.val, residuePrimePathFactor n q h active p r) := by
  classical
  have hcard : (Fintype.card P.Residues : ℝ) =
      ∏ p : P.GroupPrime, (p.val : ℝ) := by
    simp [PrimeGroups.Residues, Fintype.card_pi]
  have hsum :
      (∑ y : P.Residues, P.residuePathFactor n q h active y) =
        ∏ p : P.GroupPrime,
          ∑ r : Fin p.val, residuePrimePathFactor n q h active p r := by
    simpa [residuePathFactor_as_prime_product] using
      (Finset.prod_univ_sum
        (t := fun p : P.GroupPrime => (Finset.univ : Finset (Fin p.val)))
        (f := fun p r => residuePrimePathFactor n q h active p r)).symm
  rw [PrimeGroups.residueExpectation, hcard, hsum]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

lemma one_sub_prod_le_sum_one_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hp0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => (hfs i hi).1)
      have hp1 : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one₀
        (fun i hi => (hfs i hi).1) (fun i hi => (hfs i hi).2)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hmul : f a * (1 - ∏ i ∈ s, f i) ≤ 1 - ∏ i ∈ s, f i :=
        calc
          f a * (1 - ∏ i ∈ s, f i) ≤ 1 * (1 - ∏ i ∈ s, f i) :=
            mul_le_mul_of_nonneg_right hfa.2 (sub_nonneg.mpr hp1)
          _ = 1 - ∏ i ∈ s, f i := by ring
      nlinarith [ih hfs, hmul]

lemma card_fin_residue_divisibility_le_one (p : ℕ) (hp : 0 < p) (d : ℤ) :
    (Finset.univ.filter fun r : Fin p => (p : ℤ) ∣ (r.val : ℤ) + d).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro r hr s hs
  apply Fin.ext
  have hrdiv : (p : ℤ) ∣ (r.val : ℤ) + d := (Finset.mem_filter.mp hr).2
  have hsdiv : (p : ℤ) ∣ (s.val : ℤ) + d := (Finset.mem_filter.mp hs).2
  have hdvd : (p : ℤ) ∣ (r.val : ℤ) - (s.val : ℤ) := by
    convert dvd_sub hrdiv hsdiv using 1 <;> ring
  obtain ⟨k, hk⟩ := hdvd
  have hr0 : 0 ≤ (r.val : ℤ) := by positivity
  have hs0 : 0 ≤ (s.val : ℤ) := by positivity
  have hrlt : (r.val : ℤ) < (p : ℤ) := by exact_mod_cast r.isLt
  have hslt : (s.val : ℤ) < (p : ℤ) := by exact_mod_cast s.isLt
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp
  have hlow : -(p : ℤ) < (r.val : ℤ) - (s.val : ℤ) := by linarith
  have hhigh : (r.val : ℤ) - (s.val : ℤ) < (p : ℤ) := by linarith
  have hkzero : k = 0 := by
    by_cases hkneg : k < 0
    · have hk' : k ≤ -1 := by omega
      have hmul := mul_le_mul_of_nonneg_left hk' hpz.le
      nlinarith [hk, hmul, hlow]
    · by_cases hkpos : 0 < k
      · have hk' : 1 ≤ k := by omega
        have hmul := mul_le_mul_of_nonneg_left hk' hpz.le
        nlinarith [hk, hmul, hhigh]
      · omega
  have hnat : r.val = s.val := by
    have hd : (r.val : ℤ) - (s.val : ℤ) = 0 := by rw [hk, hkzero]; simp
    exact_mod_cast (sub_eq_zero.mp hd)
  exact hnat

lemma activeAllowedResidues_card_le_one {P : PrimeGroups} (n : ℕ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (p : P.GroupPrime) (hp : p.val ∈ activePrimeSet n active) :
    (activeAllowedResidues n h active p).card ≤ 1 := by
  classical
  have hprime : Nat.Prime p.val := by
    have hmem : p.val ∈ Finset.univ.biUnion P.primes := by
      simpa [PrimeGroups.allPrimes] using p.property
    rcases Finset.mem_biUnion.mp hmem with ⟨g, hg, hpg⟩
    exact P.prime g p.val hpg
  obtain ⟨i, hi⟩ := (mem_activePrimeSet_iff n active p.val).1 hp
  have hsub : activeAllowedResidues n h active p ⊆
      Finset.univ.filter (fun r : Fin p.val => (p.val : ℤ) ∣ (r.val : ℤ) + h i) := by
    intro r hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hr).2 i hi
  calc
    (activeAllowedResidues n h active p).card ≤
        (Finset.univ.filter (fun r : Fin p.val =>
          (p.val : ℤ) ∣ (r.val : ℤ) + h i)).card := Finset.card_le_card hsub
    _ ≤ 1 := card_fin_residue_divisibility_le_one p.val
      hprime.pos (h i)

def residueMissCoefficient {P : PrimeGroups} (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (p : P.GroupPrime) (r : Fin p.val) : ℝ :=
  1 - ∏ i : Fin (n + 1),
    if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1

def residueMissMean {P : PrimeGroups} (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (p : P.GroupPrime) : ℝ :=
  (p.val : ℝ)⁻¹ * ∑ r : Fin p.val, residueMissCoefficient n q h p r

lemma activeGroupPrimes_card_le_visits {P : PrimeGroups} (n J ell : ℕ)
    (active : Fin (n + 1) → Finset ℕ)
    (hactive : ∀ i, (active i).card ≤ (J + ell) * P.count) :
    (activeGroupPrimes (P := P) n active).card ≤
      (n + 1) * ((J + ell) * P.count) := by
  classical
  have hcardImage : (activeGroupPrimes (P := P) n active).card ≤
      (activePrimeSet n active).card := by
    apply Finset.card_le_card_of_injOn (fun p : P.GroupPrime => p.val)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp q hq hval
      exact Subtype.ext hval
  calc
    (activeGroupPrimes (P := P) n active).card ≤
        (activePrimeSet n active).card := hcardImage
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (active i).card :=
      card_biUnion_le_sum_card _ _
    _ ≤ ∑ _i : Fin (n + 1), (J + ell) * P.count := by
      apply Finset.sum_le_sum
      intro i hi
      exact hactive i
    _ = (n + 1) * ((J + ell) * P.count) := by simp

lemma residueMissCoefficient_nonneg {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) (r : Fin p.val) :
    0 ≤ residueMissCoefficient n q h p r := by
  have hprod : ∏ i : Fin (n + 1),
      (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i hi
      by_cases hdiv : (p.val : ℤ) ∣ (r.val : ℤ) + h i
      · simpa [hdiv] using (hq i).1
      · simp [hdiv]
    · intro i hi
      by_cases hdiv : (p.val : ℤ) ∣ (r.val : ℤ) + h i
      · simpa [hdiv] using (hq i).2
      · simp [hdiv]
  exact sub_nonneg.mpr hprod

lemma residueMissCoefficient_le_one {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) (r : Fin p.val) :
    residueMissCoefficient n q h p r ≤ 1 := by
  have hprod : 0 ≤ ∏ i : Fin (n + 1),
      (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1) := by
    apply Finset.prod_nonneg
    intro i hi
    split_ifs with hdiv
    · exact (hq i).1
    · norm_num
  dsimp [residueMissCoefficient]
  linarith

lemma residueMissCoefficient_le_sum_hits {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) (r : Fin p.val) :
    residueMissCoefficient n q h p r ≤
      ∑ i : Fin (n + 1),
        (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then (1 : ℝ) else 0) := by
  classical
  let f : Fin (n + 1) → ℝ := fun i =>
    if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ f i ∧ f i ≤ 1 := by
    intro i hi
    dsimp [f]
    split_ifs <;> [exact hq i; exact ⟨by norm_num, by norm_num⟩]
  have hbase := one_sub_prod_le_sum_one_sub (Finset.univ : Finset (Fin (n + 1))) f hf
  dsimp [residueMissCoefficient, f]
  calc
    1 - ∏ i : Fin (n + 1),
          (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1) ≤
        ∑ i : Fin (n + 1),
          (1 - (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then q i else 1)) := by
            simpa [f] using hbase
    _ ≤ ∑ i : Fin (n + 1),
          (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro i hi
            split_ifs with hdiv
            · linarith [(hq i).1]
            · simp

lemma sum_residueMissCoefficient_le_visits {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) :
    (∑ r : Fin p.val, residueMissCoefficient n q h p r) ≤ n + 1 := by
  classical
  calc
    (∑ r : Fin p.val, residueMissCoefficient n q h p r) ≤
        ∑ r : Fin p.val, ∑ i : Fin (n + 1),
          (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro r hr
            exact residueMissCoefficient_le_sum_hits n q h hq p r
    _ = ∑ i : Fin (n + 1), ∑ r : Fin p.val,
          (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin (n + 1), 1 := by
      apply Finset.sum_le_sum
      intro i hi
      have hsum :
          (∑ r : Fin p.val,
            (if (p.val : ℤ) ∣ (r.val : ℤ) + h i then (1 : ℝ) else 0)) =
            (Finset.univ.filter fun r : Fin p.val =>
              (p.val : ℤ) ∣ (r.val : ℤ) + h i).card := by
        simp
      rw [hsum]
      have hp : 0 < p.val := by
        have hmem : p.val ∈ Finset.univ.biUnion P.primes := by
          simpa [PrimeGroups.allPrimes] using p.property
        rcases Finset.mem_biUnion.mp hmem with ⟨g, hg, hpmem⟩
        exact (P.prime g p.val hpmem).pos
      exact_mod_cast card_fin_residue_divisibility_le_one p.val hp (h i)
    _ = n + 1 := by simp

lemma residueMissMean_bounds {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) :
    0 ≤ residueMissMean n q h p ∧
      residueMissMean n q h p ≤ (n + 1 : ℝ) / (p.val : ℝ) := by
  have hp : 0 < (p.val : ℝ) := by
    have hmem : p.val ∈ Finset.univ.biUnion P.primes := by
      simpa [PrimeGroups.allPrimes] using p.property
    rcases Finset.mem_biUnion.mp hmem with ⟨g, hg, hpg⟩
    exact_mod_cast (P.prime g p.val hpg).pos
  have hsum0 : 0 ≤ ∑ r : Fin p.val, residueMissCoefficient n q h p r :=
    Finset.sum_nonneg fun r hr => residueMissCoefficient_nonneg n q h hq p r
  have hsum := sum_residueMissCoefficient_le_visits n q h hq p
  constructor
  · dsimp [residueMissMean]
    exact mul_nonneg (inv_nonneg.mpr hp.le) hsum0
  · dsimp [residueMissMean]
    calc
      (p.val : ℝ)⁻¹ * ∑ r : Fin p.val, residueMissCoefficient n q h p r ≤
          (p.val : ℝ)⁻¹ * (n + 1 : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)
      _ = (n + 1 : ℝ) / (p.val : ℝ) := by ring

lemma log_one_sub_ge_neg_two_mul {u : ℝ} (hu0 : 0 ≤ u) (huhalf : u ≤ 1 / 2) :
    -2 * u ≤ Real.log (1 - u) := by
  have hpos : 0 < 1 - u := by linarith
  have hinvpos : 0 < (1 - u)⁻¹ := inv_pos.mpr hpos
  have hlog := Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_inv] at hlog
  have hdiv : (1 - u)⁻¹ - 1 ≤ 2 * u := by
    rw [show (1 - u)⁻¹ - 1 = u / (1 - u) by field_simp; ring]
    apply (div_le_iff₀ hpos).2
    have hmul : 0 ≤ u * (1 - 2 * u) :=
      mul_nonneg hu0 (by linarith)
    nlinarith
  linarith

lemma prod_one_sub_ge_exp_neg_two_sum {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (huhalf : ∀ i, u i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i, u i) ≤ ∏ i, (1 - u i) := by
  classical
  have hfactor_pos : ∀ i, 0 < 1 - u i := by
    intro i
    linarith [huhalf i]
  have hprod_pos : 0 < ∏ i, (1 - u i) := by
    apply Finset.prod_pos
    intro i hi
    exact hfactor_pos i
  have hlog : -2 * ∑ i, u i ≤ Real.log (∏ i, (1 - u i)) := by
    rw [Real.log_prod (s := Finset.univ) (f := fun i => 1 - u i)]
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      exact log_one_sub_ge_neg_two_mul (hu0 i) (huhalf i)
    · intro i hi
      exact ne_of_gt (hfactor_pos i)
  calc
    Real.exp (-2 * ∑ i, u i) ≤ Real.exp (Real.log (∏ i, (1 - u i))) :=
      Real.exp_le_exp.mpr hlog
    _ = ∏ i, (1 - u i) := Real.exp_log hprod_pos

lemma inactiveMissProduct_lower {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ)
    (hμ0 : ∀ p ∈ inactiveGroupPrimes (P := P) n active,
      0 ≤ residueMissMean n q h p)
    (hμhalf : ∀ p ∈ inactiveGroupPrimes (P := P) n active,
      residueMissMean n q h p ≤ 1 / 2) :
    Real.exp (-2 * ∑ p ∈ inactiveGroupPrimes (P := P) n active,
        residueMissMean n q h p) ≤
      ∏ p ∈ inactiveGroupPrimes (P := P) n active,
        (1 - residueMissMean n q h p) := by
  classical
  let U := inactiveGroupPrimes (P := P) n active
  let S := {p : P.GroupPrime // p ∈ U}
  have hprod := prod_one_sub_ge_exp_neg_two_sum
    (fun p : S => residueMissMean n q h p.val)
    (fun p => hμ0 p.val p.property)
    (fun p => hμhalf p.val p.property)
  have hsum : (∑ p : S, residueMissMean n q h p.val) =
      ∑ p ∈ U, residueMissMean n q h p := by
    change (∑ p : {p : P.GroupPrime // p ∈ U}, residueMissMean n q h p.val) = _
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach U _
  have hprodEq : (∏ p : S, (1 - residueMissMean n q h p.val)) =
      ∏ p ∈ U, (1 - residueMissMean n q h p) := by
    change (∏ p : {p : P.GroupPrime // p ∈ U}, (1 - residueMissMean n q h p.val)) = _
    rw [Finset.univ_eq_attach]
    exact Finset.prod_attach U (fun p => 1 - residueMissMean n q h p)
  rw [hsum, hprodEq] at hprod
  simpa [U] using hprod

lemma groupPrime_prime {P : PrimeGroups} (p : P.GroupPrime) : Nat.Prime p.val := by
  have hmem : p.val ∈ Finset.univ.biUnion P.primes := by
    simpa [PrimeGroups.allPrimes] using p.property
  rcases Finset.mem_biUnion.mp hmem with ⟨g, hg, hpg⟩
  exact P.prime g p.val hpg

lemma groupPrime_pairwise_coprime {P : PrimeGroups} :
    Pairwise (Function.onFun Nat.Coprime (fun p : P.GroupPrime => p.val)) := by
  intro p q hpq
  apply (Nat.coprime_primes (groupPrime_prime p) (groupPrime_prime q)).2
  intro hval
  exact hpq (Subtype.ext hval)

def finResidueOfInt (p : ℕ) [NeZero p] (z : ℤ) : Fin p :=
  (ZMod.finEquiv p).symm (z : ZMod p)

lemma finResidueOfInt_val (p : ℕ) [NeZero p] (z : ℤ) :
    (finResidueOfInt p z).val = (z : ZMod p).val := by
  dsimp [finResidueOfInt]
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => rfl

lemma finResidueOfInt_modulus_dvd (p : ℕ) [NeZero p] (z : ℤ) :
    (p : ℤ) ∣ z - ((finResidueOfInt p z).val : ℤ) := by
  have hcast : ((finResidueOfInt p z).val : ZMod p) = (z : ZMod p) := by
    rw [finResidueOfInt_val]
    exact ZMod.natCast_zmod_val (z : ZMod p)
  have hcast' : (p : ℤ) ∣ z - ((finResidueOfInt p z).val : ℤ) := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((finResidueOfInt p z).val : ℤ) z p).mp (by exact_mod_cast hcast)
  exact hcast'

lemma finEquiv_apply_eq_natCast (p : ℕ) [NeZero p] (r : Fin p) :
    ZMod.finEquiv p r = (r.val : ZMod p) := by
  have hval : (ZMod.finEquiv p r).val = r.val := by
    cases p with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ p => rfl
  have hcast := ZMod.natCast_zmod_val (ZMod.finEquiv p r)
  rw [hval] at hcast
  exact hcast.symm

lemma finResidueOfInt_eq_of_dvd (p : ℕ) [NeZero p] (z : ℤ)
    (r : Fin p) (hr : (p : ℤ) ∣ z - (r.val : ℤ)) :
    r = finResidueOfInt p z := by
  let r₀ := finResidueOfInt p z
  have hr₀ : (p : ℤ) ∣ z - (r₀.val : ℤ) := by simpa [r₀] using finResidueOfInt_modulus_dvd p z
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hrdiv : (p : ℤ) ∣ (r.val : ℤ) - z := by
    have hneg := dvd_neg.mpr hr
    simpa [sub_eq_add_neg, add_comm] using hneg
  have hr₀div : (p : ℤ) ∣ (r₀.val : ℤ) - z := by
    have hneg := dvd_neg.mpr hr₀
    simpa [sub_eq_add_neg, add_comm] using hneg
  have hrmem : r ∈ Finset.univ.filter (fun t : Fin p =>
      (p : ℤ) ∣ (t.val : ℤ) + -z) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [sub_eq_add_neg] using hrdiv⟩
  have hr₀mem : r₀ ∈ Finset.univ.filter (fun t : Fin p =>
      (p : ℤ) ∣ (t.val : ℤ) + -z) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [sub_eq_add_neg] using hr₀div⟩
  have hcard := card_fin_residue_divisibility_le_one p hp (-z)
  exact (Finset.card_le_one.mp hcard) r hrmem r₀ hr₀mem

lemma finResidue_indicator_sum_eq_one (p : ℕ) [NeZero p] (z : ℤ) :
    (∑ r : Fin p, if (p : ℤ) ∣ z - (r.val : ℤ) then (1 : ℝ) else 0) = 1 := by
  classical
  let r₀ := finResidueOfInt p z
  have hr₀ : (p : ℤ) ∣ z - (r₀.val : ℤ) := by simpa [r₀] using finResidueOfInt_modulus_dvd p z
  rw [Finset.sum_eq_single r₀]
  · simp [hr₀]
  · intro r hr hne
    have hnot : ¬ (p : ℤ) ∣ z - (r.val : ℤ) := by
      intro hdiv
      exact hne (finResidueOfInt_eq_of_dvd p z r hdiv)
    simp [hnot]
  · simp

lemma integerPrimePathFactor_one_sub_eq_miss_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) (z : ℤ)
    (hactive : ∀ i, p.val ∉ active i) :
    1 - integerPrimePathFactor n q h active p.val z =
      ∑ r : Fin p.val,
        (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
          residueMissCoefficient n q h p r else 0) := by
  classical
  haveI : NeZero p.val := ⟨(groupPrime_prime p).ne_zero⟩
  let r₀ := finResidueOfInt p.val z
  have hmod := finResidueOfInt_modulus_dvd p.val z
  have hr₀ : (p.val : ℤ) ∣ z - (r₀.val : ℤ) := by simpa [r₀] using hmod
  have hsum :
      (∑ r : Fin p.val,
        if (p.val : ℤ) ∣ z - (r.val : ℤ) then
          residueMissCoefficient n q h p r else 0) =
        residueMissCoefficient n q h p r₀ := by
    rw [Finset.sum_eq_single r₀]
    · simp [hr₀]
    · intro r hr hne
      have hnot : ¬ (p.val : ℤ) ∣ z - (r.val : ℤ) := by
        intro hdiv
        exact hne (finResidueOfInt_eq_of_dvd p.val z r hdiv)
      simp [hnot]
    · simp
  calc
    1 - integerPrimePathFactor n q h active p.val z =
        1 - residuePrimePathFactor n q h active p r₀ := by
          rw [integerPrimePathFactor_modEq n q h active p z r₀ hr₀]
    _ = residueMissCoefficient n q h p r₀ := by
          simp [residuePrimePathFactor, residueMissCoefficient, hactive]
    _ = _ := hsum.symm

lemma interval_crt_groupPrime_count_error {P : PrimeGroups}
    (s : Finset P.GroupPrime)
    (r : (i : {p // p ∈ s}) → Fin i.val.val)
    (a b : ℤ) (hab : a ≤ b) :
    abs ((({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
        (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ)) -
      (Finset.Ico a b).card /
        (∏ i : {p // p ∈ s}, i.val.val : ℝ)) ≤ 1 := by
  classical
  letI (p : P.GroupPrime) : NeZero p.val := ⟨(groupPrime_prime p).ne_zero⟩
  let m : P.GroupPrime → ℕ := fun p => p.val
  let y : (i : {p // p ∈ s}) → ZMod (m i.val) :=
    fun i => ZMod.finEquiv (m i.val) (r i)
  have hc : Pairwise (Function.onFun Nat.Coprime (fun i : {p // p ∈ s} => m i.val)) := by
    intro i j hij
    apply groupPrime_pairwise_coprime
    intro hv
    exact hij (Subtype.ext hv)
  have hcoords (z : ℤ) (i : {p // p ∈ s}) :
      ((z : ZMod (m i.val)) = y i) ↔
        (i.val.val : ℤ) ∣ z - (r i).val := by
    change ((z : ZMod (m i.val)) =
      ZMod.finEquiv (m i.val) (r i)) ↔ _
    rw [finEquiv_apply_eq_natCast]
    have hcast := ZMod.intCast_eq_intCast_iff_dvd_sub
      ((r i).val : ℤ) z (m i.val)
    constructor
    · intro hz
      apply hcast.mp
      exact_mod_cast hz.symm
    · intro hd
      exact_mod_cast (hcast.mpr hd).symm
  have hfilter :
      {z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
        (i.val.val : ℤ) ∣ z - (r i).val} =
      {z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
        (z : ZMod (m i.val)) = y i} := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hdiv⟩
      refine ⟨hz, ?_⟩
      intro i
      exact (hcoords z i).2 (hdiv i)
    · rintro ⟨hz, hcast⟩
      refine ⟨hz, ?_⟩
      intro i
      exact (hcoords z i).1 (hcast i)
  rw [hfilter]
  have hpos : ∀ i ∈ s, 0 < m i := by
    intro i hi
    exact (groupPrime_prime i).pos
  simpa [m] using interval_crt_modEq_count_error s m hpos hc y a b hab

lemma interval_crt_groupPrime_average_error {P : PrimeGroups}
    (s : Finset P.GroupPrime)
    (r : (i : {p // p ∈ s}) → Fin i.val.val)
    (a b : ℤ) (hab : a ≤ b) (hcard : 0 < (Finset.Ico a b).card) :
    abs (((Finset.Ico a b).card : ℝ)⁻¹ *
        ({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
          (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ) -
      (∏ i : {p // p ∈ s}, (i.val.val : ℝ))⁻¹) ≤
        ((Finset.Ico a b).card : ℝ)⁻¹ := by
  have hcrt := interval_crt_groupPrime_count_error s r a b hab
  let M : ℝ := (Finset.Ico a b).card
  let Q : ℝ := ∏ i : {p // p ∈ s}, (i.val.val : ℝ)
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast hcard
  have hQ : 0 < Q := by
    dsimp [Q]
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast (groupPrime_prime i.val).pos
  have hscaled :
      abs (M⁻¹ * (({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
        (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ) -
          (Finset.Ico a b).card / Q)) ≤ M⁻¹ := by
    have hInv : 0 ≤ M⁻¹ := inv_nonneg.mpr hM.le
    have hcrt' :
        abs ((({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
          (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ) -
          (Finset.Ico a b).card / Q)) ≤ 1 := by
      simpa [Q] using hcrt
    rw [abs_mul, abs_of_nonneg hInv]
    calc
      M⁻¹ * abs ((({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
          (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ) -
          (Finset.Ico a b).card / Q)) ≤ M⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hcrt' hInv
      _ = M⁻¹ := by ring
  have hEq :
      M⁻¹ * (({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
        (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ) -
          (Finset.Ico a b).card / Q) =
        M⁻¹ * ({z ∈ Finset.Ico a b | ∀ i : {p // p ∈ s},
          (i.val.val : ℤ) ∣ z - (r i).val}.card : ℝ) - Q⁻¹ := by
    dsimp [M]
    field_simp [hM.ne', hQ.ne']
  rw [← hEq]
  simpa [M, Q] using hscaled

def combineGroupPrimeResidues {P : PrimeGroups}
    (A U : Finset P.GroupPrime)
    (rA : (p : {p // p ∈ A}) → Fin p.val.val)
    (rU : (p : {p // p ∈ U}) → Fin p.val.val)
    (p : {p // p ∈ A ∪ U}) : Fin p.val.val :=
  if hp : p.val ∈ A then rA ⟨p.val, hp⟩
  else rU ⟨p.val, (Finset.mem_union.mp p.property).resolve_left hp⟩

lemma combineGroupPrimeResidues_active {P : PrimeGroups}
    (A U : Finset P.GroupPrime)
    (rA : (p : {p // p ∈ A}) → Fin p.val.val)
    (rU : (p : {p // p ∈ U}) → Fin p.val.val)
    (p : {p // p ∈ A ∪ U}) (hp : p.val ∈ A) :
    combineGroupPrimeResidues A U rA rU p = rA ⟨p.val, hp⟩ := by
  simp [combineGroupPrimeResidues, hp]

lemma combineGroupPrimeResidues_inactive {P : PrimeGroups}
    (A U : Finset P.GroupPrime) (hdisj : Disjoint A U)
    (rA : (p : {p // p ∈ A}) → Fin p.val.val)
    (rU : (p : {p // p ∈ U}) → Fin p.val.val)
    (p : {p // p ∈ A ∪ U}) (hp : p.val ∈ U) :
    combineGroupPrimeResidues A U rA rU p = rU ⟨p.val, hp⟩ := by
  have hnot : p.val ∉ A := by
    intro hA
    exact (Finset.disjoint_left.mp hdisj) hA hp
  simp [combineGroupPrimeResidues, hnot, hp]

lemma combineGroupPrimeResidues_hits_iff {P : PrimeGroups}
    (A U : Finset P.GroupPrime) (hdisj : Disjoint A U)
    (rA : (p : {p // p ∈ A}) → Fin p.val.val)
    (rU : (p : {p // p ∈ U}) → Fin p.val.val) (z : ℤ) :
    (∀ p : {p // p ∈ A ∪ U},
      (p.val.val : ℤ) ∣ z - (combineGroupPrimeResidues A U rA rU p).val) ↔
      (∀ p : {p // p ∈ A}, (p.val.val : ℤ) ∣ z - (rA p).val) ∧
      (∀ p : {p // p ∈ U}, (p.val.val : ℤ) ∣ z - (rU p).val) := by
  constructor
  · intro hall
    constructor
    · intro p
      have hp' : p.val ∈ A ∪ U := Finset.mem_union_left U p.property
      have h := hall ⟨p.val, hp'⟩
      rw [combineGroupPrimeResidues_active A U rA rU ⟨p.val, hp'⟩ p.property] at h
      exact h
    · intro p
      have hp' : p.val ∈ A ∪ U := Finset.mem_union_right A p.property
      have h := hall ⟨p.val, hp'⟩
      rw [combineGroupPrimeResidues_inactive A U hdisj rA rU ⟨p.val, hp'⟩ p.property] at h
      exact h
  · rintro ⟨hA, hU⟩ p
    rcases Finset.mem_union.mp p.property with hpA | hpU
    · rw [combineGroupPrimeResidues_active A U rA rU p hpA]
      exact hA ⟨p.val, hpA⟩
    · rw [combineGroupPrimeResidues_inactive A U hdisj rA rU p hpU]
      exact hU ⟨p.val, hpU⟩

lemma integerPrimePathFactor_as_residue_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) (z : ℤ) :
    integerPrimePathFactor n q h active p.val z =
      ∑ r : Fin p.val,
        (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
          residuePrimePathFactor n q h active p r else 0) := by
  classical
  haveI : NeZero p.val := ⟨(groupPrime_prime p).ne_zero⟩
  let r₀ := finResidueOfInt p.val z
  have hmod := finResidueOfInt_modulus_dvd p.val z
  have hr₀ : (p.val : ℤ) ∣ z - (r₀.val : ℤ) := by simpa [r₀] using hmod
  have hunique : ∀ r : Fin p.val, (p.val : ℤ) ∣ z - (r.val : ℤ) → r = r₀ := by
    intro r hr
    have hrmem : r ∈ Finset.univ.filter (fun t : Fin p.val =>
        (p.val : ℤ) ∣ (t.val : ℤ) + -z) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      convert dvd_neg.mpr hr using 1 <;> ring
    have hr₀mem : r₀ ∈ Finset.univ.filter (fun t : Fin p.val =>
        (p.val : ℤ) ∣ (t.val : ℤ) + -z) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      convert dvd_neg.mpr hr₀ using 1 <;> ring
    have hcard := card_fin_residue_divisibility_le_one p.val (groupPrime_prime p).pos (-z)
    exact (Finset.card_le_one.mp hcard) r hrmem r₀ hr₀mem
  have hsum :
      (∑ r : Fin p.val,
        if (p.val : ℤ) ∣ z - (r.val : ℤ) then
          residuePrimePathFactor n q h active p r else 0) =
        residuePrimePathFactor n q h active p r₀ := by
    rw [Finset.sum_eq_single r₀]
    · simp [hr₀]
    · intro r hr hne
      have hnot : ¬ (p.val : ℤ) ∣ z - (r.val : ℤ) := by
        intro hdiv
        exact hne (hunique r hdiv)
      simp [hnot]
    · simp
  calc
    integerPrimePathFactor n q h active p.val z =
        residuePrimePathFactor n q h active p r₀ :=
      integerPrimePathFactor_modEq n q h active p z r₀ hr₀
    _ = _ := hsum.symm

lemma integerPrimePathFactor_active_as_allowed_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) (z : ℤ) :
    integerPrimePathFactor n q h active p.val z =
      ∑ r ∈ activeAllowedResidues n h active p,
        (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
          residuePathDamping n q h active p r else 0) := by
  rw [integerPrimePathFactor_as_residue_sum]
  simp_rw [residuePrimePathFactor_as_allowed_sum]
  have hsplit (r : Fin p.val) :
      (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
        ∑ r' ∈ activeAllowedResidues n h active p,
          if r = r' then residuePathDamping n q h active p r' else 0
       else 0) =
        ∑ r' ∈ activeAllowedResidues n h active p,
          if (p.val : ℤ) ∣ z - (r.val : ℤ) then
            (if r = r' then residuePathDamping n q h active p r' else 0)
          else 0 := by
    by_cases hc : (p.val : ℤ) ∣ z - (r.val : ℤ) <;> simp [hc]
  calc
    (∑ r : Fin p.val,
      (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
        ∑ r' ∈ activeAllowedResidues n h active p,
          if r = r' then residuePathDamping n q h active p r' else 0
       else 0)) =
        ∑ r : Fin p.val, ∑ r' ∈ activeAllowedResidues n h active p,
          if (p.val : ℤ) ∣ z - (r.val : ℤ) then
            (if r = r' then residuePathDamping n q h active p r' else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hsplit r
    _ = ∑ r' ∈ activeAllowedResidues n h active p,
          ∑ r : Fin p.val,
            if (p.val : ℤ) ∣ z - (r.val : ℤ) then
              (if r = r' then residuePathDamping n q h active p r' else 0)
            else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ r' ∈ activeAllowedResidues n h active p,
          (if (p.val : ℤ) ∣ z - (r'.val : ℤ) then
            residuePathDamping n q h active p r' else 0) := by
              apply Finset.sum_congr rfl
              intro r' hr'
              rw [Finset.sum_eq_single r']
              · simp
              · intro r hr hne
                simp [hne]
              · simp

def activeAssignmentHits {P : PrimeGroups} (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ)
    (a : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val) : Prop :=
  ∀ p : {p // p ∈ activeGroupPrimes (P := P) n active},
    (p.val.val : ℤ) ∣ z - (a p.val p.property).val

def activeAssignmentWeight {P : PrimeGroups} (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (a : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val) : ℝ :=
  ∏ p ∈ (activeGroupPrimes (P := P) n active).attach,
    residuePathDamping n q h active p.val (a p.val p.property)

lemma activeAssignment_indicator_product {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ)
    (a : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val) :
    (∏ p ∈ (activeGroupPrimes (P := P) n active).attach,
      (if (p.val.val : ℤ) ∣ z - (a p.val p.property).val then
        residuePathDamping n q h active p.val (a p.val p.property) else 0)) =
      (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
        activeAssignmentWeight n q h active a := by
  classical
  by_cases hh : activeAssignmentHits n active z a
  · have hprod :
        (∏ p ∈ (activeGroupPrimes (P := P) n active).attach,
          (if (p.val.val : ℤ) ∣ z - (a p.val p.property).val then
            residuePathDamping n q h active p.val (a p.val p.property) else 0)) =
          ∏ p ∈ (activeGroupPrimes (P := P) n active).attach,
            residuePathDamping n q h active p.val (a p.val p.property) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [hh p]
    rw [if_pos hh, hprod, activeAssignmentWeight]
    simp
  · have hbad : ∃ p : {p // p ∈ activeGroupPrimes (P := P) n active},
        ¬ ((p.val.val : ℤ) ∣ z - (a p.val p.property).val) := by
      simpa [activeAssignmentHits] using hh
    obtain ⟨p, hdiv⟩ := hbad
    rw [if_neg hh]
    simp only [zero_mul]
    have hpAttach : p ∈ (activeGroupPrimes (P := P) n active).attach := by simp
    apply Finset.prod_eq_zero hpAttach
    simp [hdiv]

lemma prod_ite_zero_eq_indicator_mul_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (cond : ι → Prop) [DecidablePred cond] (w : ι → ℝ) :
    (∏ i ∈ s, if cond i then w i else 0) =
      (if ∀ i ∈ s, cond i then (1 : ℝ) else 0) * ∏ i ∈ s, w i := by
  classical
  by_cases hall : ∀ i ∈ s, cond i
  · have hprod : (∏ i ∈ s, if cond i then w i else 0) = ∏ i ∈ s, w i := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [hall i hi]
    rw [hprod, if_pos hall]
    simp
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨i, hi, hcond⟩ := hall
    rw [Finset.prod_eq_zero hi]
    · simp
    · simp [hcond]

def integerMissValue {P : PrimeGroups} (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (p : P.GroupPrime) (z : ℤ) : ℝ :=
  ∑ r ∈ (Finset.univ : Finset (Fin p.val)),
    if (p.val : ℤ) ∣ z - (r.val : ℤ) then residueMissCoefficient n q h p r else 0

lemma integerMissValue_bounds {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) (z : ℤ) :
    0 ≤ integerMissValue n q h p z ∧ integerMissValue n q h p z ≤ 1 := by
  classical
  let S := Finset.univ.filter fun r : Fin p.val =>
    (p.val : ℤ) ∣ z - (r.val : ℤ)
  have hp : 0 < p.val := (groupPrime_prime p).pos
  have hS_eq : S = Finset.univ.filter fun r : Fin p.val =>
      (p.val : ℤ) ∣ (r.val : ℤ) + (-z) := by
    ext r
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hd
      have hneg : (p.val : ℤ) ∣ -(z - (r.val : ℤ)) := dvd_neg.mpr hd
      convert hneg using 1 <;> ring
    · intro hd
      have hneg : (p.val : ℤ) ∣ -((r.val : ℤ) - z) := dvd_neg.mpr hd
      convert hneg using 1 <;> ring
  have hS_card : S.card ≤ 1 := by
    rw [hS_eq]
    exact card_fin_residue_divisibility_le_one p.val hp (-z)
  have hsum : integerMissValue n q h p z =
      ∑ r ∈ S, residueMissCoefficient n q h p r := by
    simp [integerMissValue, S, Finset.sum_filter]
  constructor
  · unfold integerMissValue
    apply Finset.sum_nonneg
    intro r hr
    split_ifs with hdiv
    · exact residueMissCoefficient_nonneg n q h hq p r
    · norm_num
  · rw [hsum]
    calc
      (∑ r ∈ S, residueMissCoefficient n q h p r) ≤ ∑ _r ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact residueMissCoefficient_le_one n q h hq p r
      _ = (S.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hS_card

def inactiveResidueAssignmentHits {P : PrimeGroups} (U : Finset P.GroupPrime)
    (z : ℤ) (a : ∀ p : P.GroupPrime, p ∈ U → Fin p.val) : Prop :=
  ∀ p : {p // p ∈ U}, (p.val.val : ℤ) ∣ z - (a p.val p.property).val

def inactiveResidueAssignmentWeight {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (U : Finset P.GroupPrime) (a : ∀ p : P.GroupPrime, p ∈ U → Fin p.val) : ℝ :=
  ∏ p ∈ U.attach, residueMissCoefficient n q h p.val (a p.val p.property)

lemma integerMissProduct_expansion {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (U : Finset P.GroupPrime) (z : ℤ) :
    (∏ p ∈ U, integerMissValue n q h p z) =
      ∑ a ∈ U.pi (fun p : P.GroupPrime => (Finset.univ : Finset (Fin p.val))),
        (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0) *
          inactiveResidueAssignmentWeight n q h U a := by
  classical
  simp_rw [integerMissValue]
  rw [Finset.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simpa [inactiveResidueAssignmentHits, inactiveResidueAssignmentWeight] using
    (prod_ite_zero_eq_indicator_mul_prod
      (s := U.attach)
      (cond := fun p : {p // p ∈ U} =>
        (p.val.val : ℤ) ∣ z - (a p.val p.property).val)
      (w := fun p : {p // p ∈ U} =>
        residueMissCoefficient n q h p.val (a p.val p.property)))

lemma inactiveResidueAssignmentWeight_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ) (U : Finset P.GroupPrime) :
    (∑ a ∈ U.pi (fun p : P.GroupPrime => (Finset.univ : Finset (Fin p.val))),
      inactiveResidueAssignmentWeight n q h U a) =
      ∏ p ∈ U, ∑ r : Fin p.val, residueMissCoefficient n q h p r := by
  classical
  simpa [inactiveResidueAssignmentWeight] using
    (Finset.prod_sum U
      (fun p : P.GroupPrime => (Finset.univ : Finset (Fin p.val)))
      (fun p r => residueMissCoefficient n q h p r)).symm

lemma active_inactive_assignment_class_average_error {P : PrimeGroups}
    (n : ℕ) (active : Fin (n + 1) → Finset ℕ) (U : Finset P.GroupPrime)
    (hdisj : Disjoint (activeGroupPrimes (P := P) n active) U)
    (rA : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val)
    (rU : ∀ p : P.GroupPrime, p ∈ U → Fin p.val)
    (lo hi : ℤ) (hlohi : lo ≤ hi) (hcard : 0 < (Finset.Ico lo hi).card) :
    abs (((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ z ∈ Finset.Ico lo hi,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            (if inactiveResidueAssignmentHits U z rU then 1 else 0) -
      (∏ i : {p // p ∈ activeGroupPrimes (P := P) n active ∪ U},
          (i.val.val : ℝ))⁻¹) ≤ ((Finset.Ico lo hi).card : ℝ)⁻¹ := by
  classical
  let A := activeGroupPrimes (P := P) n active
  let S := A ∪ U
  let rA' : (p : {p // p ∈ A}) → Fin p.val.val := fun p => rA p.val p.property
  let rU' : (p : {p // p ∈ U}) → Fin p.val.val := fun p => rU p.val p.property
  let rS : (p : {p // p ∈ S}) → Fin p.val.val :=
    fun p => combineGroupPrimeResidues A U rA' rU' p
  have hcombine := combineGroupPrimeResidues_hits_iff A U hdisj rA' rU'
  have hfilter :
      {z ∈ Finset.Ico lo hi |
        activeAssignmentHits n active z rA ∧ inactiveResidueAssignmentHits U z rU} =
      {z ∈ Finset.Ico lo hi | ∀ p : {p // p ∈ S},
        (p.val.val : ℤ) ∣ z - (rS p).val} := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hA, hU⟩
      refine ⟨hz, ?_⟩
      apply (hcombine z).mpr
      exact ⟨by simpa [activeAssignmentHits, rA'] using hA,
        by simpa [inactiveResidueAssignmentHits, rU'] using hU⟩
    · rintro ⟨hz, hS⟩
      rcases (hcombine z).mp hS with ⟨hA, hU⟩
      exact ⟨hz, by simpa [activeAssignmentHits, rA'] using hA,
        by simpa [inactiveResidueAssignmentHits, rU'] using hU⟩
  have hsum :
      (∑ z ∈ Finset.Ico lo hi,
        (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
          (if inactiveResidueAssignmentHits U z rU then 1 else 0)) =
        ({z ∈ Finset.Ico lo hi |
          activeAssignmentHits n active z rA ∧ inactiveResidueAssignmentHits U z rU}.card : ℝ) := by
    calc
      _ = ∑ z ∈ Finset.Ico lo hi,
            (if activeAssignmentHits n active z rA ∧
                inactiveResidueAssignmentHits U z rU then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro z hz
              by_cases hA : activeAssignmentHits n active z rA <;>
                by_cases hU : inactiveResidueAssignmentHits U z rU <;> simp [hA, hU]
      _ = _ := by simp
  rw [hsum, hfilter]
  exact interval_crt_groupPrime_average_error S rS lo hi hlohi hcard

lemma activeIntegerProduct_expansion {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    (∏ p ∈ activeGroupPrimes (P := P) n active,
        integerPrimePathFactor n q h active p.val z) =
      ∑ a ∈ (activeGroupPrimes (P := P) n active).pi
          (fun p : P.GroupPrime => activeAllowedResidues n h active p),
        ∏ p ∈ (activeGroupPrimes (P := P) n active).attach,
          (if (p.val.val : ℤ) ∣ z - (a p.val p.property).val then
            residuePathDamping n q h active p.val (a p.val p.property) else 0) := by
  classical
  have hlocal : ∀ p ∈ activeGroupPrimes (P := P) n active,
      integerPrimePathFactor n q h active p.val z =
        ∑ r ∈ activeAllowedResidues n h active p,
          (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
            residuePathDamping n q h active p r else 0) := by
    intro p hp
    exact integerPrimePathFactor_active_as_allowed_sum n q h active p z
  rw [Finset.prod_congr rfl hlocal]
  rw [Finset.prod_sum]

lemma activeIntegerProduct_as_hit_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    (∏ p ∈ activeGroupPrimes (P := P) n active,
        integerPrimePathFactor n q h active p.val z) =
      ∑ a ∈ (activeGroupPrimes (P := P) n active).pi
          (fun p : P.GroupPrime => activeAllowedResidues n h active p),
        (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
          activeAssignmentWeight n q h active a := by
  rw [activeIntegerProduct_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  exact activeAssignment_indicator_product n q h active z a

lemma inactiveIntegerProduct_eq_miss_product {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    (∏ p ∈ inactiveGroupPrimes (P := P) n active,
        integerPrimePathFactor n q h active p.val z) =
      ∏ p ∈ inactiveGroupPrimes (P := P) n active,
        (1 - ∑ r : Fin p.val,
          (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
            residueMissCoefficient n q h p r else 0)) := by
  apply Finset.prod_congr rfl
  intro p hp
  have hnot : p.val ∉ activePrimeSet n active := (Finset.mem_filter.mp hp).2
  have hactive : ∀ i, p.val ∉ active i := by
    intro i hi
    exact hnot ((mem_activePrimeSet_iff n active p.val).2 ⟨i, hi⟩)
  linarith [integerPrimePathFactor_one_sub_eq_miss_sum n q h active p z hactive]

lemma pathFactor_as_active_assignment_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) :
    P.pathFactor n q h active z =
      ∑ a ∈ (activeGroupPrimes (P := P) n active).pi
          (fun p : P.GroupPrime => activeAllowedResidues n h active p),
        ((if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
          activeAssignmentWeight n q h active a) *
          ∏ p ∈ inactiveGroupPrimes (P := P) n active,
            (1 - ∑ r : Fin p.val,
              (if (p.val : ℤ) ∣ z - (r.val : ℤ) then
                residueMissCoefficient n q h p r else 0)) := by
  rw [pathFactor_active_inactive_product, activeIntegerProduct_as_hit_sum,
    inactiveIntegerProduct_eq_miss_product, Finset.sum_mul]

def activeModulusReal {P : PrimeGroups} (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) : ℝ :=
  ∏ p ∈ activeGroupPrimes (P := P) n active, (p.val : ℝ)

lemma activeModulusReal_le_exp_of_card {P : PrimeGroups} (n : ℕ)
    (active : Fin (n + 1) → Finset ℕ) (K : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hcard : (activeGroupPrimes (P := P) n active).card ≤ K)
    (hprime : ∀ p ∈ activeGroupPrimes (P := P) n active, (p.val : ℝ) ≤ Real.exp y) :
    activeModulusReal (P := P) n active ≤ Real.exp ((K : ℝ) * y) := by
  classical
  let Aset := activeGroupPrimes (P := P) n active
  have hM1 : 1 ≤ Real.exp y := by
    calc
      1 ≤ 1 + y := by linarith
      _ ≤ Real.exp y := by simpa [add_comm] using Real.add_one_le_exp y
  have hprod :
      (∏ p ∈ Aset, (p.val : ℝ)) ≤ (Real.exp y) ^ Aset.card := by
    calc
      (∏ p ∈ Aset, (p.val : ℝ)) ≤ ∏ p ∈ Aset, Real.exp y := by
        apply Finset.prod_le_prod₀
        · intro p hp
          positivity
        · intro p hp
          exact hprime p hp
      _ = (Real.exp y) ^ Aset.card := by simp
  have hpow : (Real.exp y) ^ Aset.card ≤ (Real.exp y) ^ K := by
    gcongr
  have hexp := exp_nat_pow_eq y K
  calc
    activeModulusReal (P := P) n active = ∏ p ∈ Aset, (p.val : ℝ) := rfl
    _ ≤ (Real.exp y) ^ Aset.card := hprod
    _ ≤ (Real.exp y) ^ K := hpow
    _ = Real.exp ((K : ℝ) * y) := hexp

lemma activeIndependentMass_eq_modulus_inv_weight_sum {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) :
    (∏ p ∈ activeGroupPrimes (P := P) n active,
      (p.val : ℝ)⁻¹ *
        ∑ r ∈ activeAllowedResidues n h active p,
          residuePathDamping n q h active p r) =
      (activeModulusReal (P := P) n active)⁻¹ *
        ∑ a ∈ (activeGroupPrimes (P := P) n active).pi
            (fun p : P.GroupPrime => activeAllowedResidues n h active p),
          activeAssignmentWeight n q h active a := by
  classical
  calc
    (∏ p ∈ activeGroupPrimes (P := P) n active,
        (p.val : ℝ)⁻¹ *
          ∑ r ∈ activeAllowedResidues n h active p,
            residuePathDamping n q h active p r) =
        (∏ p ∈ activeGroupPrimes (P := P) n active, (p.val : ℝ)⁻¹) *
          ∏ p ∈ activeGroupPrimes (P := P) n active,
            ∑ r ∈ activeAllowedResidues n h active p,
              residuePathDamping n q h active p r := by
          rw [Finset.prod_mul_distrib]
    _ = (activeModulusReal (P := P) n active)⁻¹ *
          ∑ a ∈ (activeGroupPrimes (P := P) n active).pi
            (fun p : P.GroupPrime => activeAllowedResidues n h active p),
            activeAssignmentWeight n q h active a := by
          rw [Finset.prod_inv_distrib, Finset.prod_sum]
          rfl

lemma reciprocal_allPrimes_sum_le {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) :
    (∑ p ∈ P.allPrimes, (p : ℝ)⁻¹) ≤ (P.count : ℝ) * F.vMax := by
  classical
  rcases hP with ⟨_, _, _, _, hV, _⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset P.Group)) P.primes := by
    intro g hg k hk hne
    exact P.disjoint g k hne
  calc
    (∑ p ∈ P.allPrimes, (p : ℝ)⁻¹) =
        ∑ g : P.Group, ∑ p ∈ P.primes g, (p : ℝ)⁻¹ := by
      simpa [PrimeGroups.allPrimes] using
        (Finset.sum_biUnion hdisj (f := fun p : ℕ => (p : ℝ)⁻¹))
    _ ≤ ∑ _g : P.Group, F.vMax :=
      Finset.sum_le_sum fun g hg => (hV g).2
    _ = (P.count : ℝ) * F.vMax := by simp [mul_comm]

lemma residueMissMean_sum_le {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (n : ℕ) (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∑ p : P.GroupPrime, residueMissMean n q h p) ≤
      ((n + 1 : ℕ) : ℝ) * (P.count : ℝ) * F.vMax := by
  calc
    (∑ p : P.GroupPrime, residueMissMean n q h p) ≤
        ∑ p : P.GroupPrime, ((n + 1 : ℝ) / (p.val : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (residueMissMean_bounds n q h hq p).2
    _ = ((n + 1 : ℝ) * ∑ p : P.GroupPrime, (p.val : ℝ)⁻¹) := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum]
    _ = ((n + 1 : ℝ) * ∑ p ∈ P.allPrimes, (p : ℝ)⁻¹) := by
      congr 1
      exact groupPrime_sum_eq_allPrimes (fun p => (p : ℝ)⁻¹)
    _ ≤ ((n + 1 : ℝ) * ((P.count : ℝ) * F.vMax)) :=
      mul_le_mul_of_nonneg_left (reciprocal_allPrimes_sum_le hP) (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) * (P.count : ℝ) * F.vMax := by
      push_cast
      ring

lemma groupPrime_lower_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (hL : 1 ≤ L x) (p : P.GroupPrime) :
    Real.exp ((L x) ^ F.a) ≤ (p.val : ℝ) := by
  have hmem : p.val ∈ Finset.univ.biUnion P.primes := by
    simpa [PrimeGroups.allPrimes] using p.property
  rcases Finset.mem_biUnion.mp hmem with ⟨g, hg, hpg⟩
  rcases hP with ⟨_, _, _, _, _, hprime⟩
  have hp := hprime g p.val hpg
  cases hb : P.big g with
  | false =>
      simp [hb] at hp
      exact hp.1
  | true =>
      have hac : F.a ≤ F.c := le_of_lt (lt_trans F.ab F.bc)
      have hpow : (L x) ^ F.a ≤ (L x) ^ F.c :=
        Real.rpow_le_rpow_of_exponent_le hL hac
      simp [hb] at hp
      exact (Real.exp_le_exp.mpr hpow).trans hp.1

lemma N_add_one_le_five_L {x : ℝ} (hL : 1 ≤ L x) :
    ((N x + 1 : ℕ) : ℝ) ≤ 5 * L x := by
  have hpow : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL
      (show (52 : ℝ) / 100 ≤ (1 : ℝ) by norm_num)
  have hceil : (R x : ℝ) < (L x) ^ ((52 : ℝ) / 100) + 1 := by
    dsimp [R]
    exact Nat.ceil_lt_add_one (by positivity)
  have hN : ((N x + 1 : ℕ) : ℝ) = 2 * (R x : ℝ) + 1 := by
    simp [N]
  rw [hN]
  nlinarith [hpow, hceil]

lemma N_add_one_le_five_Lpow52 {x : ℝ} (hL : 1 ≤ L x) :
    ((N x + 1 : ℕ) : ℝ) ≤ 5 * (L x) ^ ((52 : ℝ) / 100) := by
  have hy : (1 : ℝ) ≤ (L x) ^ ((52 : ℝ) / 100) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL
      (show (0 : ℝ) ≤ (52 : ℝ) / 100 by norm_num)
    simpa using h
  have hceil : (R x : ℝ) < (L x) ^ ((52 : ℝ) / 100) + 1 := by
    dsimp [R]
    exact Nat.ceil_lt_add_one (by positivity)
  have hN : ((N x + 1 : ℕ) : ℝ) = 2 * (R x : ℝ) + 1 := by simp [N]
  rw [hN]
  nlinarith [hceil, hy]

lemma eventually_N_add_one_div_exp_a_lt_half (F : FixedData) :
    ∀ᶠ x : ℝ in atTop,
      ((N x + 1 : ℕ) : ℝ) / Real.exp ((L x) ^ F.a) < 1 / 2 := by
  have hlog : Tendsto L atTop atTop := by
    change Tendsto Real.log atTop atTop
    exact Real.tendsto_log_atTop
  have hpow : Tendsto (fun x : ℝ => (L x) ^ F.a) atTop atTop :=
    (tendsto_rpow_atTop F.a_pos).comp hlog
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero F.a⁻¹ (1 : ℝ) (by norm_num)).comp hpow
  have hsmall : ∀ᶠ x : ℝ in atTop,
      ((L x) ^ F.a) ^ F.a⁻¹ * Real.exp (-((L x) ^ F.a)) < 1 / 10 :=
    by
      simpa [one_mul] using
        hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))
  have hLlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := hlog.eventually_ge_atTop 1
  filter_upwards [hsmall, hLlarge] with x hsmallx hLx
  have hpowEq : ((L x) ^ F.a) ^ F.a⁻¹ = L x :=
    Real.rpow_rpow_inv (le_trans (by norm_num) hLx) F.a_pos.ne'
  have hN := N_add_one_le_five_L hLx
  have hratio : ((N x + 1 : ℕ) : ℝ) / Real.exp ((L x) ^ F.a) =
      ((N x + 1 : ℕ) : ℝ) * Real.exp (-((L x) ^ F.a)) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [hratio]
  calc
    ((N x + 1 : ℕ) : ℝ) * Real.exp (-((L x) ^ F.a)) ≤
        (5 * L x) * Real.exp (-((L x) ^ F.a)) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ = 5 * (((L x) ^ F.a) ^ F.a⁻¹ * Real.exp (-((L x) ^ F.a))) := by
      rw [hpowEq]
      ring
    _ < 1 / 2 := by nlinarith

lemma residueMissMean_le_half_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (hLx : 1 ≤ L x)
    (hsmall : ((N x + 1 : ℕ) : ℝ) / Real.exp ((L x) ^ F.a) < 1 / 2)
    (n : ℕ) (hn : n ≤ N x) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (p : P.GroupPrime) :
    residueMissMean n q h p ≤ 1 / 2 := by
  have hpLower := groupPrime_lower_of_admissible hP hLx p
  have hNumerator : 0 ≤ ((N x + 1 : ℕ) : ℝ) := by positivity
  have hExp : 0 < Real.exp ((L x) ^ F.a) := Real.exp_pos _
  have hnR : (n + 1 : ℝ) ≤ ((N x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  calc
    residueMissMean n q h p ≤ (n + 1 : ℝ) / (p.val : ℝ) :=
      (residueMissMean_bounds n q h hq p).2
    _ ≤ ((N x + 1 : ℕ) : ℝ) / (p.val : ℝ) := by
      exact div_le_div_of_nonneg_right hnR (by positivity)
    _ ≤ ((N x + 1 : ℕ) : ℝ) / Real.exp ((L x) ^ F.a) :=
      div_le_div_of_nonneg_left hNumerator hExp hpLower
    _ ≤ 1 / 2 := le_of_lt hsmall

lemma residuePrimePathFactor_eq_one_sub_miss {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) (r : Fin p.val)
    (hactive : ∀ i, p.val ∉ active i) :
    residuePrimePathFactor n q h active p r =
      1 - residueMissCoefficient n q h p r := by
  simp [residuePrimePathFactor, residueMissCoefficient, hactive]

lemma residuePrimeExpectationFactor_eq_one_sub_missMean {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime)
    (hactive : ∀ i, p.val ∉ active i) :
    (p.val : ℝ)⁻¹ *
        ∑ r : Fin p.val, residuePrimePathFactor n q h active p r =
      1 - residueMissMean n q h p := by
  rw [Finset.sum_congr rfl (fun r hr => residuePrimePathFactor_eq_one_sub_miss n q h active p r hactive)]
  rw [Finset.sum_sub_distrib]
  have hcard : (∑ _r : Fin p.val, (1 : ℝ)) = (p.val : ℝ) := by simp
  rw [hcard]
  dsimp [residueMissMean]
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast (groupPrime_prime p).ne_zero
  field_simp [hp]

lemma residueExpectation_eq_prod_one_sub_missMean {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ)
    (hactive : ∀ i, active i = ∅) :
    P.residueExpectation n q h active =
      ∏ p : P.GroupPrime, (1 - residueMissMean n q h p) := by
  rw [residueExpectation_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  apply residuePrimeExpectationFactor_eq_one_sub_missMean
  intro i
  rw [hactive i]
  simp

lemma residueExpectation_lower_of_no_active {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (hLx : 1 ≤ L x)
    (hsmall : ((N x + 1 : ℕ) : ℝ) / Real.exp ((L x) ^ F.a) < 1 / 2)
    (q : Fin (N x + 1) → ℝ) (h : Fin (N x + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (active : Fin (N x + 1) → Finset ℕ) (hactive : ∀ i, active i = ∅) :
    Real.exp (-2 * ∑ p : P.GroupPrime, residueMissMean (N x) q h p) ≤
      P.residueExpectation (N x) q h active := by
  rw [residueExpectation_eq_prod_one_sub_missMean _ _ _ _ hactive]
  apply prod_one_sub_ge_exp_neg_two_sum
  · intro p
    exact (residueMissMean_bounds (N x) q h hq p).1
  · intro p
    exact residueMissMean_le_half_of_admissible hP hLx hsmall (N x) le_rfl q h hq p

lemma residuePrimeExpectationFactor_active_split {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (p : P.GroupPrime) :
    (p.val : ℝ)⁻¹ *
        ∑ r : Fin p.val, residuePrimePathFactor n q h active p r =
      if p.val ∈ activePrimeSet n active then
        (p.val : ℝ)⁻¹ *
          ∑ r ∈ activeAllowedResidues n h active p, residuePathDamping n q h active p r
      else 1 - residueMissMean n q h p := by
  by_cases hp : p.val ∈ activePrimeSet n active
  · simpa [hp] using residuePrimePathExpectationFactor_as_allowed_sum n q h active p
  · have hnone : ∀ i, p.val ∉ active i := by
      intro i hi
      exact hp ((mem_activePrimeSet_iff n active p.val).2 ⟨i, hi⟩)
    simpa [hp] using residuePrimeExpectationFactor_eq_one_sub_missMean n q h active p hnone

lemma residueExpectation_active_inactive_factorization {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) :
    P.residueExpectation n q h active =
      (∏ p ∈ activeGroupPrimes (P := P) n active,
        (p.val : ℝ)⁻¹ *
          ∑ r ∈ activeAllowedResidues n h active p,
            residuePathDamping n q h active p r) *
      ∏ p ∈ inactiveGroupPrimes (P := P) n active,
        (1 - residueMissMean n q h p) := by
  classical
  rw [residueExpectation_factorization]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.univ : Finset P.GroupPrime))
    (p := fun p => p.val ∈ activePrimeSet n active)
    (f := fun p => (p.val : ℝ)⁻¹ *
      ∑ r : Fin p.val, residuePrimePathFactor n q h active p r)]
  simp only [activeGroupPrimes, inactiveGroupPrimes]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    simpa [(Finset.mem_filter.mp hp).2] using
      residuePrimeExpectationFactor_active_split n q h active p
  · apply Finset.prod_congr rfl
    intro p hp
    have hnot : p.val ∉ activePrimeSet n active := (Finset.mem_filter.mp hp).2
    simpa [hnot] using residuePrimeExpectationFactor_active_split n q h active p

lemma inactiveResidueAssignmentWeight_bounds {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (U : Finset P.GroupPrime)
    (a : ∀ p : P.GroupPrime, p ∈ U → Fin p.val) :
    0 ≤ inactiveResidueAssignmentWeight n q h U a ∧
      inactiveResidueAssignmentWeight n q h U a ≤ 1 := by
  classical
  constructor
  · simp only [inactiveResidueAssignmentWeight]
    apply Finset.prod_nonneg
    intro p hp
    exact residueMissCoefficient_nonneg n q h hq p.val (a p.val p.property)
  · simp only [inactiveResidueAssignmentWeight]
    apply Finset.prod_le_one₀
    · intro p hp
      exact residueMissCoefficient_nonneg n q h hq p.val (a p.val p.property)
    · intro p hp
      exact residueMissCoefficient_le_one n q h hq p.val (a p.val p.property)

lemma inactiveResidueAssignment_card {P : PrimeGroups} (U : Finset P.GroupPrime) :
    (U.pi (fun p : P.GroupPrime => (Finset.univ : Finset (Fin p.val)))).card =
      ∏ p ∈ U, p.val := by
  simp

lemma active_inactive_miss_monomial_average_error {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (active : Fin (n + 1) → Finset ℕ) (U : Finset P.GroupPrime)
    (hdisj : Disjoint (activeGroupPrimes (P := P) n active) U)
    (rA : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val)
    (lo hi : ℤ) (hlohi : lo ≤ hi) (hcard : 0 < (Finset.Ico lo hi).card) :
    abs (((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ z ∈ Finset.Ico lo hi,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            ∏ p ∈ U, integerMissValue n q h p z -
      (activeModulusReal (P := P) n active)⁻¹ *
        ∏ p ∈ U, residueMissMean n q h p) ≤
      ((Finset.Ico lo hi).card : ℝ)⁻¹ * ∏ p ∈ U, (p.val : ℝ) := by
  classical
  let I := Finset.Ico lo hi
  let M : ℝ := (I.card : ℝ)
  let A := activeGroupPrimes (P := P) n active
  let S := A ∪ U
  let B := U.pi (fun p : P.GroupPrime => (Finset.univ : Finset (Fin p.val)))
  have hM : 0 < M := by
    dsimp [M, I]
    exact_mod_cast hcard
  have hM0 : 0 ≤ M⁻¹ := inv_nonneg.mpr hM.le
  have hmodA : 0 < activeModulusReal (P := P) n active := by
    unfold activeModulusReal
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (groupPrime_prime p).pos
  have hmodU : 0 < ∏ p ∈ U, (p.val : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (groupPrime_prime p).pos
  have hmodSub :
      (∏ i : {p // p ∈ S}, (i.val.val : ℝ)) =
        activeModulusReal (P := P) n active * ∏ p ∈ U, (p.val : ℝ) := by
    calc
      (∏ i : {p // p ∈ S}, (i.val.val : ℝ)) =
          ∏ p ∈ S, (p.val : ℝ) := by
            simpa using (Finset.prod_coe_sort S (fun p : P.GroupPrime => (p.val : ℝ)))
      _ = (∏ p ∈ A, (p.val : ℝ)) * ∏ p ∈ U, (p.val : ℝ) := by
            rw [Finset.prod_union hdisj]
      _ = activeModulusReal (P := P) n active * ∏ p ∈ U, (p.val : ℝ) := by
            rfl
  have hmodInv :
      (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹ =
        (activeModulusReal (P := P) n active)⁻¹ *
          ∏ p ∈ U, (p.val : ℝ)⁻¹ := by
    rw [hmodSub, mul_inv]
    rw [Finset.prod_inv_distrib]
  have hprodMeans :
      ∏ p ∈ U, residueMissMean n q h p =
        (∏ p ∈ U, (p.val : ℝ)⁻¹) *
          ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a := by
    rw [inactiveResidueAssignmentWeight_sum]
    simp_rw [residueMissMean]
    rw [Finset.prod_mul_distrib]
  have hmeanExpand :
      (activeModulusReal (P := P) n active)⁻¹ *
          ∏ p ∈ U, residueMissMean n q h p =
        ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
          (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹ := by
    rw [hprodMeans, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← hmodInv]
    ring
  have hactualExpand :
      M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            ∏ p ∈ U, integerMissValue n q h p z =
        ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
          (M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) := by
    have hsum :
        ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              ∏ p ∈ U, integerMissValue n q h p z =
          ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
            ∑ z ∈ I,
              (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0) := by
      calc
        _ = ∑ z ∈ I, ∑ a ∈ B,
              ((if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) *
                  inactiveResidueAssignmentWeight n q h U a := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [integerMissProduct_expansion, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = ∑ a ∈ B, ∑ z ∈ I,
              ((if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) *
                  inactiveResidueAssignmentWeight n q h U a := by
              rw [Finset.sum_comm]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z hz
              ring
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hdiff :
      abs (∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
          ((M⁻¹ * ∑ z ∈ I,
              (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) -
            (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹)) ≤
        M⁻¹ * (B.card : ℝ) := by
    calc
      _ ≤ ∑ a ∈ B,
            abs (inactiveResidueAssignmentWeight n q h U a *
              ((M⁻¹ * ∑ z ∈ I,
                  (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                    (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) -
                (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹)) := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ B, M⁻¹ := by
            apply Finset.sum_le_sum
            intro a ha
            rw [abs_mul]
            have hweight := inactiveResidueAssignmentWeight_bounds n q h hq U a
            have herr := active_inactive_assignment_class_average_error n active U hdisj
              rA a lo hi hlohi hcard
            calc
              |inactiveResidueAssignmentWeight n q h U a| *
                    |M⁻¹ * ∑ z ∈ I,
                      (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                        (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0) -
                      (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹| ≤
                  1 * M⁻¹ := by
                    calc
                      _ ≤ 1 *
                          |M⁻¹ * ∑ z ∈ I,
                            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                              (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0) -
                            (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹| :=
                          mul_le_mul_of_nonneg_right
                            (abs_le.mpr ⟨by linarith [hweight.1], hweight.2⟩)
                            (abs_nonneg _)
                      _ ≤ 1 * M⁻¹ :=
                          mul_le_mul_of_nonneg_left herr (by norm_num)
              _ = M⁻¹ := by ring
      _ = M⁻¹ * (B.card : ℝ) := by simp [mul_comm]
  have hcardB : (B.card : ℝ) = ∏ p ∈ U, (p.val : ℝ) := by
    exact_mod_cast (inactiveResidueAssignment_card U)
  have htarget :
      (activeModulusReal (P := P) n active)⁻¹ *
          ∏ p ∈ U, residueMissMean n q h p =
        ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
          (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹ := hmeanExpand
  rw [show (Finset.Ico lo hi : Finset ℤ) = I by rfl,
    show ((Finset.Ico lo hi).card : ℝ)⁻¹ = M⁻¹ by rfl,
    hactualExpand, htarget]
  have hrewrite :
      (∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
          (M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0))) -
        ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
          (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹ =
      ∑ a ∈ B, inactiveResidueAssignmentWeight n q h U a *
        ((M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) -
          (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹) := by
    symm
    calc
      _ = ∑ a ∈ B,
            (inactiveResidueAssignmentWeight n q h U a *
                (M⁻¹ * ∑ z ∈ I,
                  (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                    (if inactiveResidueAssignmentHits U z a then (1 : ℝ) else 0)) -
              inactiveResidueAssignmentWeight n q h U a *
                (∏ i : {p // p ∈ S}, (i.val.val : ℝ))⁻¹) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hrewrite]
  simpa [I, M, hcardB, mul_comm] using hdiff

lemma active_inactive_miss_elementary_average_error {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (active : Fin (n + 1) → Finset ℕ) (U : Finset P.GroupPrime)
    (hdisj : Disjoint (activeGroupPrimes (P := P) n active) U)
    (rA : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val)
    (lo hi : ℤ) (hlohi : lo ≤ hi) (hcard : 0 < (Finset.Ico lo hi).card)
    (k : ℕ) :
    abs (((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ z ∈ Finset.Ico lo hi,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            elementarySymmetric (fun p => integerMissValue n q h p z) U k -
      (activeModulusReal (P := P) n active)⁻¹ *
        elementarySymmetric (fun p => residueMissMean n q h p) U k) ≤
      ((Finset.Ico lo hi).card : ℝ)⁻¹ *
        elementarySymmetric (fun p => (p.val : ℝ)) U k := by
  classical
  let I := Finset.Ico lo hi
  let M : ℝ := (I.card : ℝ)
  let A := activeGroupPrimes (P := P) n active
  let V := U.powersetCard k
  have hM : 0 < M := by
    dsimp [M, I]
    exact_mod_cast hcard
  have hM0 : 0 ≤ M⁻¹ := inv_nonneg.mpr hM.le
  have hsumActual :
      ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            elementarySymmetric (fun p => integerMissValue n q h p z) U k =
        ∑ v ∈ V, ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            ∏ p ∈ v, integerMissValue n q h p z := by
    calc
      _ = ∑ z ∈ I, ∑ v ∈ V,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              ∏ p ∈ v, integerMissValue n q h p z := by
              apply Finset.sum_congr rfl
              intro z hz
              simp only [elementarySymmetric]
              rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_comm]
  have hactualExpand :
      M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            elementarySymmetric (fun p => integerMissValue n q h p z) U k =
        ∑ v ∈ V, M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            ∏ p ∈ v, integerMissValue n q h p z := by
    rw [hsumActual, Finset.mul_sum]
  have hmeanExpand :
      (activeModulusReal (P := P) n active)⁻¹ *
          elementarySymmetric (fun p => residueMissMean n q h p) U k =
        ∑ v ∈ V, (activeModulusReal (P := P) n active)⁻¹ *
          ∏ p ∈ v, residueMissMean n q h p := by
    simp only [elementarySymmetric]
    rw [Finset.mul_sum]
  have herrorSum :
      abs (∑ v ∈ V,
        ((M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              ∏ p ∈ v, integerMissValue n q h p z) -
          (activeModulusReal (P := P) n active)⁻¹ *
            ∏ p ∈ v, residueMissMean n q h p)) ≤
        M⁻¹ * ∑ v ∈ V, ∏ p ∈ v, (p.val : ℝ) := by
    calc
      _ ≤ ∑ v ∈ V,
          abs ((M⁻¹ * ∑ z ∈ I,
              (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                ∏ p ∈ v, integerMissValue n q h p z) -
            (activeModulusReal (P := P) n active)⁻¹ *
              ∏ p ∈ v, residueMissMean n q h p) := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ V, M⁻¹ * ∏ p ∈ v, (p.val : ℝ) := by
            apply Finset.sum_le_sum
            intro v hv
            have hvsub : v ⊆ U := (Finset.mem_powersetCard.mp hv).1
            have hdv : Disjoint A v := hdisj.mono_right hvsub
            simpa [I, M] using
              active_inactive_miss_monomial_average_error n q h hq active v hdv rA
                lo hi hlohi hcard
      _ = M⁻¹ * ∑ v ∈ V, ∏ p ∈ v, (p.val : ℝ) := by
            rw [Finset.mul_sum]
  rw [show (Finset.Ico lo hi : Finset ℤ) = I by rfl,
    show ((Finset.Ico lo hi).card : ℝ)⁻¹ = M⁻¹ by rfl,
    hactualExpand, hmeanExpand]
  have hsumDiff :
      (∑ v ∈ V,
        M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            ∏ p ∈ v, integerMissValue n q h p z) -
        ∑ v ∈ V,
          (activeModulusReal (P := P) n active)⁻¹ *
            ∏ p ∈ v, residueMissMean n q h p =
      ∑ v ∈ V,
        ((M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              ∏ p ∈ v, integerMissValue n q h p z) -
          (activeModulusReal (P := P) n active)⁻¹ *
            ∏ p ∈ v, residueMissMean n q h p) := by
    symm
    calc
      _ = ∑ v ∈ V,
            (M⁻¹ * ∑ z ∈ I,
                (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                  ∏ p ∈ v, integerMissValue n q h p z -
              (activeModulusReal (P := P) n active)⁻¹ *
                ∏ p ∈ v, residueMissMean n q h p) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hsumDiff]
  simpa [I, M, elementarySymmetric] using herrorSum

lemma active_inactive_miss_truncation_average_error {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (active : Fin (n + 1) → Finset ℕ) (U : Finset P.GroupPrime)
    (hdisj : Disjoint (activeGroupPrimes (P := P) n active) U)
    (rA : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val)
    (lo hi : ℤ) (hlohi : lo ≤ hi) (hcard : 0 < (Finset.Ico lo hi).card)
    (H : ℕ) :
    abs (((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ z ∈ Finset.Ico lo hi,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            inclusionTruncation (fun p => integerMissValue n q h p z) U H -
      (activeModulusReal (P := P) n active)⁻¹ *
        inclusionTruncation (fun p => residueMissMean n q h p) U H) ≤
      ((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (H + 1),
          elementarySymmetric (fun p => (p.val : ℝ)) U k := by
  classical
  let I := Finset.Ico lo hi
  let M : ℝ := (I.card : ℝ)
  let K := Finset.range (H + 1)
  have hsumActual :
      ∑ z ∈ I,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            inclusionTruncation (fun p => integerMissValue n q h p z) U H =
        ∑ k ∈ K, (-1 : ℝ) ^ k *
          ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              elementarySymmetric (fun p => integerMissValue n q h p z) U k := by
    calc
      _ = ∑ z ∈ I, ∑ k ∈ K,
            (-1 : ℝ) ^ k *
              ((if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                elementarySymmetric (fun p => integerMissValue n q h p z) U k) := by
              apply Finset.sum_congr rfl
              intro z hz
              simp only [inclusionTruncation]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = ∑ k ∈ K, ∑ z ∈ I,
            (-1 : ℝ) ^ k *
              ((if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                elementarySymmetric (fun p => integerMissValue n q h p z) U k) := by
              rw [Finset.sum_comm]
      _ = _ := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mul_sum]
  have hactualExpand :
      ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ z ∈ I,
            (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
              inclusionTruncation (fun p => integerMissValue n q h p z) U H =
        ∑ k ∈ K, (-1 : ℝ) ^ k *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
            ∑ z ∈ I,
              (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                elementarySymmetric (fun p => integerMissValue n q h p z) U k) := by
    rw [hsumActual, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hmeanExpand :
      (activeModulusReal (P := P) n active)⁻¹ *
          inclusionTruncation (fun p => residueMissMean n q h p) U H =
        ∑ k ∈ K, (-1 : ℝ) ^ k *
          ((activeModulusReal (P := P) n active)⁻¹ *
            elementarySymmetric (fun p => residueMissMean n q h p) U k) := by
    simp only [inclusionTruncation]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [show (Finset.Ico lo hi : Finset ℤ) = I by rfl,
    hactualExpand, hmeanExpand]
  have hterm : ∀ k ∈ K,
      abs (((-1 : ℝ) ^ k) *
            (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ z ∈ I,
                (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                  elementarySymmetric (fun p => integerMissValue n q h p z) U k) -
            ((-1 : ℝ) ^ k) *
              ((activeModulusReal (P := P) n active)⁻¹ *
                elementarySymmetric (fun p => residueMissMean n q h p) U k)) ≤
        ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          elementarySymmetric (fun p => (p.val : ℝ)) U k := by
    intro k hk
    rw [← mul_sub, abs_mul]
    have hbase := active_inactive_miss_elementary_average_error n q h hq active U
      hdisj rA lo hi hlohi hcard k
    have hsign : |(-1 : ℝ) ^ k| = 1 := by simp
    rw [hsign, one_mul]
    simpa [I] using hbase
  have hsumDiff :
      (∑ k ∈ K, (-1 : ℝ) ^ k *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
            ∑ z ∈ I,
              (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                elementarySymmetric (fun p => integerMissValue n q h p z) U k)) -
        ∑ k ∈ K, (-1 : ℝ) ^ k *
          ((activeModulusReal (P := P) n active)⁻¹ *
            elementarySymmetric (fun p => residueMissMean n q h p) U k) =
      ∑ k ∈ K,
        (((-1 : ℝ) ^ k) *
            (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ z ∈ I,
                (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                  elementarySymmetric (fun p => integerMissValue n q h p z) U k) -
          ((-1 : ℝ) ^ k) *
            ((activeModulusReal (P := P) n active)⁻¹ *
              elementarySymmetric (fun p => residueMissMean n q h p) U k)) := by
    symm
    rw [Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ K,
          abs (((-1 : ℝ) ^ k) *
              (((Finset.Ico lo hi).card : ℝ)⁻¹ *
                ∑ z ∈ I,
                  (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
                    elementarySymmetric (fun p => integerMissValue n q h p z) U k) -
              ((-1 : ℝ) ^ k) *
                ((activeModulusReal (P := P) n active)⁻¹ *
                  elementarySymmetric (fun p => residueMissMean n q h p) U k)) := by
          rw [hsumDiff]
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ K, elementarySymmetric (fun p => (p.val : ℝ)) U k := by
          calc
            _ ≤ ∑ k ∈ K,
                ((Finset.Ico lo hi).card : ℝ)⁻¹ *
                  elementarySymmetric (fun p => (p.val : ℝ)) U k :=
              Finset.sum_le_sum fun k hk => hterm k hk
            _ = _ := by rw [Finset.mul_sum]

lemma active_inactive_miss_product_average_error {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (active : Fin (n + 1) → Finset ℕ) (U : Finset P.GroupPrime)
    (hdisj : Disjoint (activeGroupPrimes (P := P) n active) U)
    (rA : ∀ p : P.GroupPrime, p ∈ activeGroupPrimes (P := P) n active → Fin p.val)
    (hμ : ∀ p ∈ U, 0 ≤ residueMissMean n q h p ∧ residueMissMean n q h p ≤ 1)
    (lambdaTot : ℝ) (hlambdaTot : 0 ≤ lambdaTot)
    (hlambdaTotsum : (∑ p ∈ U, residueMissMean n q h p) ≤ lambdaTot)
    (lo hi : ℤ) (hlohi : lo ≤ hi) (hcard : 0 < (Finset.Ico lo hi).card)
    (H : ℕ) (hHeven : H % 2 = 0) :
    abs (((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ z ∈ Finset.Ico lo hi,
          (if activeAssignmentHits n active z rA then (1 : ℝ) else 0) *
            ∏ p ∈ U, (1 - integerMissValue n q h p z) -
      (activeModulusReal (P := P) n active)⁻¹ *
        ∏ p ∈ U, (1 - residueMissMean n q h p)) ≤
      ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (H + 1),
            elementarySymmetric (fun p => (p.val : ℝ)) U k +
        ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (H + 2),
            elementarySymmetric (fun p => (p.val : ℝ)) U k +
        (activeModulusReal (P := P) n active)⁻¹ *
          (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
  classical
  let I := Finset.Ico lo hi
  let M : ℝ := (I.card : ℝ)
  let X : P.GroupPrime → ℤ → ℝ := fun p z => integerMissValue n q h p z
  let Xz (z : ℤ) : P.GroupPrime → ℝ := fun p => X p z
  let μ : P.GroupPrime → ℝ := fun p => residueMissMean n q h p
  let ind : ℤ → ℝ := fun z => if activeAssignmentHits n active z rA then 1 else 0
  have hMpos : 0 < M := by
    dsimp [M, I]
    exact_mod_cast hcard
  have hM0 : 0 ≤ M⁻¹ := inv_nonneg.mpr hMpos.le
  have hQpos : 0 < activeModulusReal (P := P) n active := by
    unfold activeModulusReal
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (groupPrime_prime p).pos
  have hQ0 : 0 ≤ (activeModulusReal (P := P) n active)⁻¹ :=
    inv_nonneg.mpr hQpos.le
  have hX : ∀ p ∈ U, ∀ z, 0 ≤ X p z ∧ X p z ≤ 1 := by
    intro p hp z
    exact integerMissValue_bounds n q h hq p z
  have hμ' : ∀ p ∈ U, 0 ≤ μ p ∧ μ p ≤ 1 := by
    simpa [μ] using hμ
  have hHsuccEven : (H + 1) % 2 = 1 := by omega
  have hstep : inclusionTruncation μ U H - inclusionTruncation μ U (H + 1) =
      elementarySymmetric μ U (H + 1) := by
    have hdiv : H = 2 * (H / 2) := by omega
    have hHone : H + 1 = 2 * (H / 2) + 1 := congrArg (fun t : ℕ => t + 1) hdiv
    have hsign : (-1 : ℝ) ^ (H + 1) = -1 := by
      calc
        (-1 : ℝ) ^ (H + 1) = (-1 : ℝ) ^ (2 * (H / 2) + 1) :=
          congrArg (fun t : ℕ => (-1 : ℝ) ^ t) hHone
        _ = (-1 : ℝ) ^ (2 * (H / 2)) * (-1 : ℝ) := by rw [pow_succ]
        _ = ((-1 : ℝ) ^ 2) ^ (H / 2) * (-1 : ℝ) := by rw [← pow_mul]
        _ = -1 := by norm_num
    rw [inclusionTruncation_succ, hsign]
    ring
  have hμsumNonneg : 0 ≤ ∑ p ∈ U, μ p :=
    Finset.sum_nonneg fun p hp => (hμ' p hp).1
  have htailElem :
      elementarySymmetric μ U (H + 1) ≤
        lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ) := by
    have hbound := elementarySymmetric_bound μ U
      (fun p hp => (hμ' p hp).1) (H + 1)
    calc
      elementarySymmetric μ U (H + 1) ≤
          (∑ p ∈ U, μ p) ^ (H + 1) / ((H + 1).factorial : ℝ) := hbound
      _ ≤ lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ hμsumNonneg hlambdaTotsum (H + 1)
  have htail0 : 0 ≤ lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ) := by positivity
  have hXupper (z : ℤ) :
      ∏ p ∈ U, (1 - X p z) ≤ inclusionTruncation (Xz z) U H := by
    apply (inclusionTruncation_bonferroni (Xz z) U (fun p hp => hX p hp z) H).1
    exact hHeven
  have hXlower (z : ℤ) :
      inclusionTruncation (Xz z) U (H + 1) ≤ ∏ p ∈ U, (1 - X p z) := by
    apply (inclusionTruncation_bonferroni (Xz z) U (fun p hp => hX p hp z) (H + 1)).2
    exact hHsuccEven
  have hμupper : ∏ p ∈ U, (1 - μ p) ≤ inclusionTruncation μ U H := by
    apply (inclusionTruncation_bonferroni μ U hμ' H).1
    exact hHeven
  have hμlower : inclusionTruncation μ U (H + 1) ≤ ∏ p ∈ U, (1 - μ p) := by
    apply (inclusionTruncation_bonferroni μ U hμ' (H + 1)).2
    exact hHsuccEven
  let avgProd : ℝ := M⁻¹ * ∑ z ∈ I, ind z * ∏ p ∈ U, (1 - X p z)
  let avgHigh : ℝ := M⁻¹ * ∑ z ∈ I, ind z * inclusionTruncation (Xz z) U H
  let avgLow : ℝ := M⁻¹ * ∑ z ∈ I, ind z * inclusionTruncation (Xz z) U (H + 1)
  let meanProd : ℝ := (activeModulusReal (P := P) n active)⁻¹ *
    ∏ p ∈ U, (1 - μ p)
  let meanHigh : ℝ := (activeModulusReal (P := P) n active)⁻¹ * inclusionTruncation μ U H
  let meanLow : ℝ := (activeModulusReal (P := P) n active)⁻¹ *
    inclusionTruncation μ U (H + 1)
  have havgHigh : avgProd ≤ avgHigh := by
    dsimp [avgProd, avgHigh]
    apply mul_le_mul_of_nonneg_left _ hM0
    apply Finset.sum_le_sum
    intro z hz
    by_cases hzA : activeAssignmentHits n active z rA
    · simpa [ind, hzA, X] using hXupper z
    · simp [ind, hzA]
  have havgLow : avgLow ≤ avgProd := by
    dsimp [avgLow, avgProd]
    apply mul_le_mul_of_nonneg_left _ hM0
    apply Finset.sum_le_sum
    intro z hz
    by_cases hzA : activeAssignmentHits n active z rA
    · simpa [ind, hzA, X] using hXlower z
    · simp [ind, hzA]
  have hmeanLow : meanLow ≤ meanProd := by
    dsimp [meanLow, meanProd]
    exact mul_le_mul_of_nonneg_left hμlower hQ0
  have hmeanHigh : meanProd ≤ meanHigh := by
    dsimp [meanHigh, meanProd]
    exact mul_le_mul_of_nonneg_left hμupper hQ0
  have htail : meanHigh - meanLow ≤
      (activeModulusReal (P := P) n active)⁻¹ *
        (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
    dsimp [meanHigh, meanLow]
    rw [← mul_sub, hstep]
    exact mul_le_mul_of_nonneg_left htailElem hQ0
  have errH :
      |avgHigh - meanHigh| ≤ M⁻¹ *
        ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k := by
    simpa [avgHigh, meanHigh, I, M, ind, X, Xz, μ] using
      active_inactive_miss_truncation_average_error n q h hq active U hdisj rA
        lo hi hlohi hcard H
  have errHsucc :
      |avgLow - meanLow| ≤ M⁻¹ *
        ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k := by
    simpa [avgLow, meanLow, I, M, ind, X, Xz, μ] using
      active_inactive_miss_truncation_average_error n q h hq active U hdisj rA
        lo hi hlohi hcard (H + 1)
  let E0 := M⁻¹ *
    ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k
  let E1 := M⁻¹ *
    ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k
  have hE0 : 0 ≤ E0 := by
    dsimp [E0]
    apply mul_nonneg hM0
    apply Finset.sum_nonneg
    intro k hk
    unfold elementarySymmetric
    apply Finset.sum_nonneg
    intro v hv
    exact Finset.prod_nonneg fun p hp => by positivity
  have hE1 : 0 ≤ E1 := by
    dsimp [E1]
    apply mul_nonneg hM0
    apply Finset.sum_nonneg
    intro k hk
    unfold elementarySymmetric
    apply Finset.sum_nonneg
    intro v hv
    exact Finset.prod_nonneg fun p hp => by positivity
  have hupper : avgProd - meanProd ≤ E0 + E1 +
      (activeModulusReal (P := P) n active)⁻¹ *
        (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
    have hmain : avgHigh - meanHigh ≤ E0 := by
      dsimp [E0]
      exact (abs_le.mp errH).2
    dsimp [avgProd, meanProd] at havgHigh hmeanLow ⊢
    dsimp [avgHigh, meanLow, E0, E1] at hmain htail ⊢
    calc
      _ ≤ avgHigh - meanLow := by linarith
      _ = (avgHigh - meanHigh) + (meanHigh - meanLow) := by ring
      _ ≤ E0 + E1 +
          (activeModulusReal (P := P) n active)⁻¹ *
            (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
          have hE1' : 0 ≤ E1 := by positivity
          linarith
  have hlower : meanProd - avgProd ≤ E0 + E1 +
      (activeModulusReal (P := P) n active)⁻¹ *
        (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
    have hmain : meanLow - avgLow ≤ E1 := by
      dsimp [E1]
      have h := (abs_le.mp errHsucc).1
      linarith
    dsimp [avgProd, meanProd] at havgLow hmeanHigh ⊢
    dsimp [avgLow, meanHigh, E0, E1] at hmain htail ⊢
    calc
      _ ≤ meanHigh - avgLow := by linarith
      _ = (meanHigh - meanLow) + (meanLow - avgLow) := by ring
      _ ≤ E0 + E1 +
          (activeModulusReal (P := P) n active)⁻¹ *
            (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
          have hE0' : 0 ≤ E0 := by positivity
          linarith
  rw [show (Finset.Ico lo hi : Finset ℤ) = I by rfl,
    show ((Finset.Ico lo hi).card : ℝ)⁻¹ = M⁻¹ by rfl]
  change |avgProd - meanProd| ≤ _
  rw [abs_le]
  constructor <;> linarith

lemma activeAssignmentWeight_nonneg {P : PrimeGroups} (n : ℕ)
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (a : ∀ p : P.GroupPrime,
      p ∈ activeGroupPrimes (P := P) n active → Fin p.val) :
    0 ≤ activeAssignmentWeight n q h active a := by
  classical
  unfold activeAssignmentWeight
  apply Finset.prod_nonneg
  intro p hp
  unfold residuePathDamping
  apply Finset.prod_nonneg
  intro i hi
  by_cases hactive : p.val.val ∈ active i
  · simp [hactive]
  · by_cases hdiv : (p.val.val : ℤ) ∣ (a p.val p.property).val + h i
    · simp [hactive, hdiv, (hq i).1]
    · simp [hactive, hdiv]

lemma scaled_errors_to_relative_budget {A S lambdaTot Q errCRT tail prod : ℝ}
    (hQ : 0 < Q) (hprod : Real.exp (-2 * lambdaTot) ≤ prod)
    (hCRT : Q * errCRT ≤ Real.exp (-A * S - 2 * lambdaTot - 4))
    (hTail : tail ≤ Real.exp (-A * S - 2 * lambdaTot - 4)) :
    errCRT + Q⁻¹ * tail ≤ Real.exp (-A * S) * (Q⁻¹ * prod) := by
  have hExp4 : 2 ≤ Real.exp (4 : ℝ) := by
    calc
      2 ≤ 1 + 4 := by norm_num
      _ ≤ Real.exp 4 := by simpa [add_comm] using Real.add_one_le_exp (4 : ℝ)
  have hFactor : 2 * Real.exp (-4 : ℝ) ≤ 1 := by
    rw [Real.exp_neg]
    exact (div_le_one (Real.exp_pos (4 : ℝ))).2 hExp4
  let t : ℝ := -A * S - 2 * lambdaTot
  have hsum : Real.exp (t - 4) + Real.exp (t - 4) ≤ Real.exp t := by
    have hmul : Real.exp (t - 4) = Real.exp t * Real.exp (-4 : ℝ) := by
      rw [show t - 4 = t + (-4) by ring, Real.exp_add]
    calc
      Real.exp (t - 4) + Real.exp (t - 4) =
          Real.exp t * (2 * Real.exp (-4 : ℝ)) := by rw [hmul]; ring
      _ ≤ Real.exp t * 1 := mul_le_mul_of_nonneg_left hFactor (Real.exp_pos _).le
      _ = Real.exp t := by ring
  have hscaled : Q * errCRT + tail ≤ Real.exp (-A * S - 2 * lambdaTot) := by
    calc
      _ ≤ Real.exp (t - 4) + Real.exp (t - 4) := by
          exact add_le_add (by simpa [t] using hCRT) (by simpa [t] using hTail)
      _ ≤ Real.exp t := hsum
      _ = Real.exp (-A * S - 2 * lambdaTot) := by rfl
  have hQinv : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQ.le
  calc
    errCRT + Q⁻¹ * tail = Q⁻¹ * (Q * errCRT + tail) := by
      field_simp [hQ.ne']
    _ ≤ Q⁻¹ * Real.exp (-A * S - 2 * lambdaTot) :=
      mul_le_mul_of_nonneg_left hscaled hQinv
    _ = Real.exp (-A * S) * (Q⁻¹ * Real.exp (-2 * lambdaTot)) := by
      rw [show -A * S - 2 * lambdaTot = (-A * S) + (-2 * lambdaTot) by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (-A * S) * (Q⁻¹ * prod) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hprod hQinv
      · positivity

lemma uniform_residue_replacement_of_error_budget {P : PrimeGroups}
    (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (active : Fin (n + 1) → Finset ℕ)
    (hμ : ∀ p ∈ inactiveGroupPrimes (P := P) n active,
      0 ≤ residueMissMean n q h p ∧ residueMissMean n q h p ≤ 1)
    (lambdaTot : ℝ) (hlambdaTot : 0 ≤ lambdaTot)
    (hlambdaTotsum :
      (∑ p ∈ inactiveGroupPrimes (P := P) n active, residueMissMean n q h p) ≤
        lambdaTot)
    (lo hi : ℤ) (hlohi : lo ≤ hi) (hcard : 0 < (Finset.Ico lo hi).card)
    (H : ℕ) (hHeven : H % 2 = 0)
    (eps : ℝ) (heps : 0 ≤ eps)
    (herr :
      ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (H + 1),
            elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ))
              (inactiveGroupPrimes (P := P) n active) k +
        ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (H + 2),
            elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ))
              (inactiveGroupPrimes (P := P) n active) k +
        (activeModulusReal (P := P) n active)⁻¹ *
          (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) ≤
      eps * (activeModulusReal (P := P) n active)⁻¹ *
        ∏ p ∈ inactiveGroupPrimes (P := P) n active,
          (1 - residueMissMean n q h p)) :
    abs (((Finset.Ico lo hi).card : ℝ)⁻¹ *
        ∑ z ∈ Finset.Ico lo hi, P.pathFactor n q h active z -
      P.residueExpectation n q h active) ≤
      eps * P.residueExpectation n q h active := by
  classical
  let I := Finset.Ico lo hi
  let M : ℝ := (I.card : ℝ)
  let Aset := activeGroupPrimes (P := P) n active
  let U := inactiveGroupPrimes (P := P) n active
  let B := Aset.pi (fun p : P.GroupPrime => activeAllowedResidues n h active p)
  let w := fun (a : ∀ p : P.GroupPrime, p ∈ Aset → Fin p.val) =>
    activeAssignmentWeight n q h active a
  let base := (activeModulusReal (P := P) n active)⁻¹ *
    ∏ p ∈ U, (1 - residueMissMean n q h p)
  have hM0 : 0 ≤ M⁻¹ := by
    dsimp [M, I]
    exact inv_nonneg.mpr (by exact_mod_cast hcard.le)
  have hdisj : Disjoint Aset U := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpU
    exact (Finset.mem_filter.mp hpU).2 ((Finset.mem_filter.mp hpA).2)
  have hweight : ∀ a ∈ B, 0 ≤ w a := by
    intro a ha
    exact activeAssignmentWeight_nonneg n q h active hq a
  have hpathExpand :
      M⁻¹ * ∑ z ∈ I, P.pathFactor n q h active z =
        ∑ a ∈ B, w a * (M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
            ∏ p ∈ U, (1 - integerMissValue n q h p z)) := by
    have hsum :
        ∑ z ∈ I, P.pathFactor n q h active z =
          ∑ a ∈ B, w a * ∑ z ∈ I,
            (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
              ∏ p ∈ U, (1 - integerMissValue n q h p z) := by
      calc
        _ = ∑ z ∈ I, ∑ a ∈ B,
              ((if activeAssignmentHits n active z a then (1 : ℝ) else 0) * w a) *
                ∏ p ∈ U, (1 - integerMissValue n q h p z) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [pathFactor_as_active_assignment_sum]
              apply Finset.sum_congr rfl
              intro a ha
              by_cases hh : activeAssignmentHits n active z a
              · simp [hh, w, U, integerMissValue]
              · simp [hh, w, U, integerMissValue]
        _ = ∑ a ∈ B, ∑ z ∈ I,
              ((if activeAssignmentHits n active z a then (1 : ℝ) else 0) * w a) *
                ∏ p ∈ U, (1 - integerMissValue n q h p z) := by
              rw [Finset.sum_comm]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z hz
              ring
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hmeanExpand : P.residueExpectation n q h active =
      ∑ a ∈ B, w a * base := by
    rw [residueExpectation_active_inactive_factorization]
    rw [activeIndependentMass_eq_modulus_inv_weight_sum]
    calc
      _ = ∑ a ∈ B,
            ((activeModulusReal (P := P) n active)⁻¹ * ∏ p ∈ U,
              (1 - residueMissMean n q h p)) * w a := by
              calc
                _ = ((activeModulusReal (P := P) n active)⁻¹ *
                      ∏ p ∈ U, (1 - residueMissMean n q h p)) *
                    ∑ a ∈ B, activeAssignmentWeight n q h active a := by ring
                _ = _ := by rw [Finset.mul_sum]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [base, w]
            ring
  have hterm : ∀ a ∈ B,
      abs ((M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
            ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base) ≤
        ((Finset.Ico lo hi).card : ℝ)⁻¹ *
            ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k +
          ((Finset.Ico lo hi).card : ℝ)⁻¹ *
            ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k +
          (activeModulusReal (P := P) n active)⁻¹ *
            (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) := by
    intro a ha
    have hμ' : ∀ p ∈ U, 0 ≤ residueMissMean n q h p ∧
        residueMissMean n q h p ≤ 1 := by simpa [U] using hμ
    have hprod := active_inactive_miss_product_average_error n q h hq active U hdisj a
      hμ' lambdaTot hlambdaTot hlambdaTotsum lo hi hlohi hcard H hHeven
    simpa [I, M, base] using hprod
  have hweightedErr : ∀ a ∈ B,
      abs (w a *
          ((M⁻¹ * ∑ z ∈ I,
              (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
                ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base)) ≤
        w a *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            ((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            (activeModulusReal (P := P) n active)⁻¹ *
              (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ))) := by
    intro a ha
    rw [abs_mul]
    have hw := hweight a ha
    have hta := hterm a ha
    calc
      |w a| * |(M⁻¹ * ∑ z ∈ I,
          (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
            ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base| ≤
        w a * |(M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
              ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base| :=
          mul_le_mul_of_nonneg_right
            (abs_le.mpr ⟨by linarith [hw], by rfl⟩) (abs_nonneg _)
      _ ≤ w a *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            ((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            (activeModulusReal (P := P) n active)⁻¹ *
              (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hta hw
  have hdiff :
      abs (∑ a ∈ B, w a *
          ((M⁻¹ * ∑ z ∈ I,
              (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
                ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base)) ≤
        ∑ a ∈ B, w a *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            ((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            (activeModulusReal (P := P) n active)⁻¹ *
              (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ))) := by
    calc
      _ ≤ ∑ a ∈ B,
          abs (w a *
            ((M⁻¹ * ∑ z ∈ I,
                (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
                  ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base)) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum hweightedErr
  change |M⁻¹ * ∑ z ∈ I, P.pathFactor n q h active z -
    P.residueExpectation n q h active| ≤ eps * P.residueExpectation n q h active
  rw [hpathExpand, hmeanExpand]
  have hrewrite :
      (∑ a ∈ B, w a *
          (M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
              ∏ p ∈ U, (1 - integerMissValue n q h p z))) -
        ∑ a ∈ B, w a * base =
      ∑ a ∈ B, w a *
        ((M⁻¹ * ∑ z ∈ I,
            (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
              ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base) := by
    symm
    calc
      _ = ∑ a ∈ B,
            (w a * (M⁻¹ * ∑ z ∈ I,
                (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
                  ∏ p ∈ U, (1 - integerMissValue n q h p z)) - w a * base) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hrewrite]
  have herrorBase :
      ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (H + 1),
            elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ)) U k +
        ((Finset.Ico lo hi).card : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (H + 2),
            elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ)) U k +
        (activeModulusReal (P := P) n active)⁻¹ *
          (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) ≤ eps * base := by
    have herrAssoc :
        ((Finset.Ico lo hi).card : ℝ)⁻¹ *
            ∑ k ∈ Finset.range (H + 1),
              elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ)) U k +
          ((Finset.Ico lo hi).card : ℝ)⁻¹ *
            ∑ k ∈ Finset.range (H + 2),
              elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ)) U k +
          (activeModulusReal (P := P) n active)⁻¹ *
            (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)) ≤
        eps * ((activeModulusReal (P := P) n active)⁻¹ *
          ∏ p ∈ U, (1 - residueMissMean n q h p)) := by
      convert herr using 1 <;> ring
    calc
      _ ≤ eps * ((activeModulusReal (P := P) n active)⁻¹ *
          ∏ p ∈ U, (1 - residueMissMean n q h p)) := herrAssoc
      _ = eps * base := by simp [base]
  have hbudget :
      (∑ a ∈ B, w a *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            ((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            (activeModulusReal (P := P) n active)⁻¹ *
              (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)))) ≤
        ∑ a ∈ B, w a * (eps * base) := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left herrorBase (hweight a ha)
  have hsumBound :
      abs (∑ a ∈ B, w a *
          ((M⁻¹ * ∑ z ∈ I,
              (if activeAssignmentHits n active z a then (1 : ℝ) else 0) *
                ∏ p ∈ U, (1 - integerMissValue n q h p z)) - base)) ≤
        eps * ∑ a ∈ B, w a * base := by
    calc
      _ ≤ ∑ a ∈ B, w a *
          (((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            ((Finset.Ico lo hi).card : ℝ)⁻¹ *
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k +
            (activeModulusReal (P := P) n active)⁻¹ *
              (lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ))) := hdiff
      _ ≤ ∑ a ∈ B, w a * (eps * base) := hbudget
      _ = eps * ∑ a ∈ B, w a * base := by
            calc
              _ = ∑ a ∈ B, eps * (w a * base) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    ring
              _ = _ := by rw [← Finset.mul_sum]
  simpa [hmeanExpand] using hsumBound

set_option maxHeartbeats 1000000 in
theorem uniform_residue_replacement_proof (F : FixedData) (J : ℕ) (A gamma : ℝ)
    (hA : 0 < A) (hgamma : 0 < gamma) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (P : PrimeGroups), P.Admissible F x →
      ∀ (h : Fin (N x + 1) → ℤ) (active : Fin (N x + 1) → Finset ℕ),
      (∀ i, active i ⊆ P.allPrimes ∧
        (active i).card ≤ (J + F.ell) * P.count) →
      ∀ X : ℝ, x ^ gamma ≤ X → X ≤ x ^ gamma⁻¹ →
      |((dyad X).card : ℝ)⁻¹ * ∑ z ∈ dyad X,
          P.pathFactor (N x) (visitQ F.q (N x)) h active z -
          P.residueExpectation (N x) (visitQ F.q (N x)) h active| ≤
        Real.exp (-A * N x * T x) *
          P.residueExpectation (N x) (visitQ F.q (N x)) h active := by
  classical
    let cLambda : ℝ := 4 * F.C₀ * F.vMax
    let Ktr : ℝ := Real.exp 1 * cLambda +
        (A + 2 * cLambda + 1) / Real.log 2 + 1
    let cActive : ℝ := 10 * F.C₀ * ((J + F.ell : ℕ) : ℝ)
    let cCRT : ℝ := cActive + 3 * (10 * Ktr + 3) + 3
    let cScale : ℝ := 5 * (A + 2 * cLambda) + 4
    let delta : ℝ := (48 : ℝ) / 100 - F.d
    have hF_d_pos : 0 < F.d :=
      lt_trans F.a_pos (lt_trans F.ab (lt_trans F.bc F.cd))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdelta : 0 < delta := by dsimp [delta]; linarith [F.d_lt]
    have hcLambda : 0 < cLambda := by
      dsimp [cLambda]
      positivity [F.C₀_pos, F.vMax_pos]
    have hKtr : 0 < Ktr := by
      dsimp [Ktr]
      positivity [hA, hcLambda, hlog2]
    have hcActive : 0 < cActive := by
      dsimp [cActive]
      positivity [F.C₀_pos, F.ell_pos]
    have hcCRT : 0 < cCRT := by
      dsimp [cCRT]
      positivity [hcActive, hKtr]
    have hcScale : 0 < cScale := by
      dsimp [cScale]
      positivity [hA, hcLambda]
    have hLtop : Tendsto L atTop atTop := by
      change Tendsto Real.log atTop atTop
      exact Real.tendsto_log_atTop
    have hTtop : Tendsto T atTop atTop := by
      change Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop
      exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have hXpowTop : Tendsto (fun x : ℝ => x ^ gamma) atTop atTop :=
      tendsto_rpow_atTop hgamma
    have hL_event : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := hLtop.eventually_ge_atTop 1
    have hT_event : ∀ᶠ x : ℝ in atTop, 2 ≤ T x := hTtop.eventually_ge_atTop 2
    have hX_event : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ gamma := hXpowTop.eventually_ge_atTop 2
    have hmiss_event := eventually_N_add_one_div_exp_a_lt_half F
    have hprimeExp_event := eventually_const_mul_L_le_exp_Lpow
      (6 * F.C₀) F.d (by positivity [F.C₀_pos]) hF_d_pos
    have hdegreeExp_event := eventually_const_mul_L_rpow_le_exp_L_rpow
      (10 * Ktr + 4) 2 F.d (by positivity [hKtr]) (by norm_num) hF_d_pos
    have hCRT_ratio_event : ∀ᶠ x : ℝ in atTop,
        T x / (L x) ^ delta < gamma / (4 * cCRT) := by
      have h := tendsto_T_div_L_rpow delta hdelta
      exact h.eventually (Iio_mem_nhds (div_pos hgamma (by positivity [hcCRT])))
    have hScale_ratio_event : ∀ᶠ x : ℝ in atTop,
        T x / (L x) ^ ((48 : ℝ) / 100) < gamma / (4 * cScale) := by
      have h := tendsto_T_div_L_rpow ((48 : ℝ) / 100) (by norm_num)
      exact h.eventually (Iio_mem_nhds (div_pos hgamma (by positivity [hcScale])))
    have hGood : ∀ᶠ x : ℝ in atTop,
        1 ≤ L x ∧ 2 ≤ T x ∧ 2 ≤ x ^ gamma ∧
          ((N x + 1 : ℕ) : ℝ) / Real.exp ((L x) ^ F.a) < 1 / 2 ∧
          6 * F.C₀ * L x ≤ Real.exp ((L x) ^ F.d) ∧
          (10 * Ktr + 4) * (L x) ^ (2 : ℝ) ≤ Real.exp ((L x) ^ F.d) ∧
          T x / (L x) ^ delta < gamma / (4 * cCRT) ∧
          T x / (L x) ^ ((48 : ℝ) / 100) < gamma / (4 * cScale) := by
      filter_upwards [hL_event, hT_event, hX_event, hmiss_event, hprimeExp_event,
        hdegreeExp_event, hCRT_ratio_event, hScale_ratio_event]
        with x hL hT hxPow hmiss hprimeExp hdegreeExp hCRTsmall hScalesmall
      exact ⟨hL, hT, hxPow, hmiss, hprimeExp, hdegreeExp, hCRTsmall, hScalesmall⟩
    obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 hGood
    refine ⟨max x0 2, ?_⟩
    intro x hx P hP h active hactive X hXlo hXhi
    have hx0' : x0 ≤ x := le_trans (le_max_left x0 2) hx
    have hxTwo : 2 ≤ x := le_trans (le_max_right x0 2) hx
    obtain ⟨hL, hT, hxPow, hsmallMiss, hPrimeExp, hDegreeExp, hCRTsmall, hScalesmall⟩ :=
      hx0 x hx0'
    let n := N x
    let q : Fin (n + 1) → ℝ := visitQ F.q n
    let NT : ℝ := (n : ℝ) * T x
    let lambdaTot : ℝ := cLambda * NT
    let H : ℕ := 2 * Nat.ceil (Ktr * NT)
    let y : ℝ := (L x) ^ F.d
    let U := inactiveGroupPrimes (P := P) n active
    let Q := activeModulusReal (P := P) n active
    let Kactive : ℕ := (n + 1) * ((J + F.ell) * P.count)
    have hxpos : 0 < x := by linarith
    have hpow52_one : 1 ≤ (L x) ^ ((52 : ℝ) / 100) := by
      have hpow := Real.rpow_le_rpow_of_exponent_le hL
        (show (0 : ℝ) ≤ (52 : ℝ) / 100 by norm_num)
      simpa using hpow
    have hRcast : 1 ≤ (R x : ℝ) := by
      dsimp [R]
      exact le_trans hpow52_one (by exact_mod_cast (Nat.le_ceil ((L x) ^ ((52 : ℝ) / 100))))
    have hNcast : (n : ℝ) = 2 * (R x : ℝ) := by simp [n, N]
    have hnTwo : 2 ≤ (n : ℝ) := by rw [hNcast]; nlinarith [hRcast]
    have hNT0 : 0 ≤ NT := by dsimp [NT]; positivity
    have hNT4 : 4 ≤ NT := by
      dsimp [NT]
      nlinarith [mul_nonneg (sub_nonneg.mpr hnTwo) (sub_nonneg.mpr hT)]
    have hNsharp : ((n + 1 : ℕ) : ℝ) ≤ 5 * (L x) ^ ((52 : ℝ) / 100) := by
      simpa [n] using N_add_one_le_five_Lpow52 hL
    have hNle : (n : ℝ) ≤ 5 * (L x) ^ ((52 : ℝ) / 100) := by
      dsimp [n]
      exact le_trans (by norm_num : (N x : ℝ) ≤ (N x + 1 : ℕ)) hNsharp
    have hTleL : T x ≤ L x := by
      dsimp [T]
      have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L x)
      linarith
    have hpow52_le_L : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
      simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
        (show (52 : ℝ) / 100 ≤ 1 by norm_num)
    have hNTle5 : NT ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x := by
      dsimp [NT]
      exact mul_le_mul_of_nonneg_right hNle (by positivity)
    have hNTleL2 : NT ≤ 5 * (L x) ^ 2 := by
      calc
        NT ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x := hNTle5
        _ ≤ 5 * L x * L x := by gcongr
        _ = 5 * (L x) ^ 2 := by rw [pow_two]; ring
    have hLambda0 : 0 ≤ lambdaTot := by dsimp [lambdaTot]; positivity
    have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := by
      intro i
      exact visitQ_bounds n i
    have hactiveCardVisit : ∀ i, (active i).card ≤ (J + F.ell) * P.count := by
      intro i
      exact (hactive i).2
    have hActiveCard := activeGroupPrimes_card_le_visits n J F.ell active hactiveCardVisit
    have hActiveCard' : (activeGroupPrimes (P := P) n active).card ≤ Kactive := by
      simpa [Kactive] using hActiveCard
    have hKactiveCast : (Kactive : ℝ) ≤ cActive *
        (L x) ^ ((52 : ℝ) / 100) * T x := by
      dsimp [Kactive, cActive]
      push_cast
      have hPcount := group_count_le_two_C0_mul_T hP
      have hJell0 : 0 ≤ (J : ℝ) + (F.ell : ℝ) := by positivity
      have hP0 : 0 ≤ (P.count : ℝ) := by positivity
      have hNsharp' : (n : ℝ) + 1 ≤ 5 * (L x) ^ ((52 : ℝ) / 100) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hNsharp
      calc
        _ ≤ 5 * (L x) ^ ((52 : ℝ) / 100) *
            (((J : ℝ) + (F.ell : ℝ)) * (P.count : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hNsharp'
                (mul_nonneg hJell0 hP0)
        _ = 5 * (L x) ^ ((52 : ℝ) / 100) *
            ((J : ℝ) + (F.ell : ℝ)) * (P.count : ℝ) := by ring
        _ ≤ 5 * (L x) ^ ((52 : ℝ) / 100) *
            ((J : ℝ) + (F.ell : ℝ)) * (2 * F.C₀ * T x) := by
              apply mul_le_mul_of_nonneg_left hPcount
              positivity
        _ = _ := by ring
    have hY0 : 0 ≤ y := by dsimp [y]; positivity
    have hYone : 1 ≤ y := by
      dsimp [y]
      have hpow := Real.rpow_le_rpow_of_exponent_le hL
        (show (0 : ℝ) ≤ F.d by exact le_of_lt hF_d_pos)
      simpa using hpow
    have hExpY2 : 2 ≤ Real.exp y := by
      calc
        2 ≤ 1 + y := by linarith
        _ ≤ Real.exp y := by simpa [add_comm] using Real.add_one_le_exp y
    have hExp3Y4 : 4 ≤ Real.exp (3 * y) := by
      calc
        4 ≤ 1 + 3 * y := by nlinarith [hYone]
        _ ≤ Real.exp (3 * y) := by simpa [add_comm] using Real.add_one_le_exp (3 * y)
    have hKactive := activeModulusReal_le_exp_of_card n active Kactive y hY0 hActiveCard'
      (fun p hp => groupPrime_upper_of_admissible hP hL p)
    have hQpos : 0 < Q := by
      dsimp [Q, activeModulusReal]
      apply Finset.prod_pos
      intro p hp
      exact_mod_cast (groupPrime_prime p).pos
    have hQinv : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQpos.le
    have hQ := hKactive
    have hmu0 : ∀ p ∈ U, 0 ≤ residueMissMean n q h p := by
      intro p hp
      exact (residueMissMean_bounds n q h hq p).1
    have hmuHalf : ∀ p ∈ U, residueMissMean n q h p ≤ 1 / 2 := by
      intro p hp
      exact residueMissMean_le_half_of_admissible hP hL hsmallMiss n le_rfl q h hq p
    have hmu : ∀ p ∈ U, 0 ≤ residueMissMean n q h p ∧
        residueMissMean n q h p ≤ 1 := by
      intro p hp
      exact ⟨hmu0 p hp, le_trans (hmuHalf p hp) (by norm_num)⟩
    have hmuSumAll := residueMissMean_sum_le hP n q h hq
    have hmuSumSubset : (∑ p ∈ U, residueMissMean n q h p) ≤
        (∑ p : P.GroupPrime, residueMissMean n q h p) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg U.subset_univ
        (by intro p hp hnot; exact (residueMissMean_bounds n q h hq p).1)
    have hn1 : 1 ≤ n := by
      exact_mod_cast (show (1 : ℝ) ≤ (n : ℝ) by linarith [hnTwo])
    have hNplusNat : n + 1 ≤ 2 * n := by omega
    have hNplusCast : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hNplusNat
    have hPcount := group_count_le_two_C0_mul_T hP
    have hmuSum : (∑ p ∈ U, residueMissMean n q h p) ≤ lambdaTot := by
      calc
        (∑ p ∈ U, residueMissMean n q h p) ≤
            (∑ p : P.GroupPrime, residueMissMean n q h p) := hmuSumSubset
        _ ≤ ((n + 1 : ℕ) : ℝ) * (P.count : ℝ) * F.vMax := hmuSumAll
        _ ≤ 2 * (n : ℝ) * (2 * F.C₀ * T x) * F.vMax := by
          have hNP : ((n + 1 : ℕ) : ℝ) * (P.count : ℝ) ≤
              2 * (n : ℝ) * (2 * F.C₀ * T x) := by
            calc
              _ ≤ 2 * (n : ℝ) * (P.count : ℝ) :=
                mul_le_mul_of_nonneg_right hNplusCast (by positivity)
              _ ≤ 2 * (n : ℝ) * (2 * F.C₀ * T x) :=
                mul_le_mul_of_nonneg_left hPcount (by positivity)
          exact mul_le_mul_of_nonneg_right hNP (F.vMax_pos.le)
        _ = lambdaTot := by dsimp [lambdaTot, cLambda, NT]; ring
    have hprodLower := inactiveMissProduct_lower n q h active hmu0 hmuHalf
    have hNplusExp : ((N x + 1 : ℕ) : ℝ) ≤ 5 * L x := by
      exact N_add_one_le_five_L hL
    have hTcount : (P.count : ℝ) ≤ 2 * F.C₀ * L x := by
      calc
        (P.count : ℝ) ≤ 2 * F.C₀ * T x := hPcount
        _ ≤ 2 * F.C₀ * L x :=
          mul_le_mul_of_nonneg_left hTleL (by positivity [F.C₀_pos])
    have hPcountExp : 3 * (P.count : ℝ) ≤ 6 * F.C₀ * L x := by
      calc
        3 * (P.count : ℝ) ≤ 3 * (2 * F.C₀ * L x) :=
          mul_le_mul_of_nonneg_left hTcount (by norm_num)
        _ = 6 * F.C₀ * L x := by ring
    have hYPrimeExp : 6 * F.C₀ * L x ≤ Real.exp y := by simpa [y] using hPrimeExp
    have hprimeFactor : 3 * (P.count : ℝ) ≤ Real.exp y := hPcountExp.trans hYPrimeExp
    have hSigmaSubset : (∑ p ∈ U, (p.val : ℝ)) ≤
        (∑ p : P.GroupPrime, (p.val : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg U.subset_univ
        (by intro p hp hnot; positivity)
    have hSigma : (∑ p ∈ U, (p.val : ℝ)) ≤ Real.exp (3 * y) := by
      calc
        (∑ p ∈ U, (p.val : ℝ)) ≤ (∑ p : P.GroupPrime, (p.val : ℝ)) := hSigmaSubset
        _ = (∑ p ∈ P.allPrimes, (p : ℝ)) := groupPrime_sum_eq_allPrimes (fun p => (p : ℝ))
        _ ≤ 3 * (P.count : ℝ) * Real.exp (2 * y) := by
          simpa [y] using allPrimes_sum_le_exp_bound hP hL
        _ ≤ Real.exp y * Real.exp (2 * y) :=
          mul_le_mul_of_nonneg_right hprimeFactor (Real.exp_pos _).le
        _ = Real.exp (3 * y) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hSigmaExp := hSigma
    have hNpow52 : (n : ℝ) ≤ 5 * (L x) ^ ((52 : ℝ) / 100) := by linarith [hNsharp]
    have hNTplus2 : (n : ℝ) * T x ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x :=
      mul_le_mul_of_nonneg_right hNpow52 (by positivity)
    have hNTcoarse : (n : ℝ) * T x ≤ 5 * (L x) ^ 2 := by
      calc
        (n : ℝ) * T x ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x := hNTplus2
        _ ≤ 5 * L x * L x := by gcongr
        _ = 5 * (L x) ^ 2 := by rw [pow_two]; ring
    have hTtwo : (L x) ^ ((52 : ℝ) / 100) * T x ≥ 1 := by
      have hTge1 : 1 ≤ T x := by linarith
      calc
        1 = (1 : ℝ) * 1 := by ring
        _ ≤ (L x) ^ ((52 : ℝ) / 100) * T x :=
          mul_le_mul hpow52_one hTge1 (by norm_num) (by linarith)
    have hceilArg : 0 ≤ Ktr * NT := by positivity
    have hceilLower : Ktr * NT ≤ (Nat.ceil (Ktr * NT) : ℝ) := by exact_mod_cast Nat.le_ceil (Ktr * NT)
    have hceilUpper : (Nat.ceil (Ktr * NT) : ℝ) < Ktr * NT + 1 :=
      Nat.ceil_lt_add_one hceilArg
    have hHeven : H % 2 = 0 := by simp [H]
    have hHdegLower : 2 * Ktr * NT ≤ ((H + 1 : ℕ) : ℝ) := by
      dsimp [H]
      push_cast
      have h2ceil : 2 * (Ktr * NT) ≤ 2 * (Nat.ceil (Ktr * NT) : ℝ) :=
        mul_le_mul_of_nonneg_left hceilLower (by norm_num)
      calc
        2 * Ktr * NT = 2 * (Ktr * NT) := by ring
        _ ≤ 2 * (Nat.ceil (Ktr * NT) : ℝ) := h2ceil
        _ ≤ 2 * (Nat.ceil (Ktr * NT) : ℝ) + 1 := by linarith
    have hHdegUpper : ((H + 1 : ℕ) : ℝ) ≤ (10 * Ktr + 3) *
        (L x) ^ ((52 : ℝ) / 100) * T x := by
      dsimp [H]
      push_cast
      let B : ℝ := (L x) ^ ((52 : ℝ) / 100) * T x
      have hB : 1 ≤ B := by simpa [B] using hTtwo
      have hceilUpper' : (Nat.ceil (Ktr * NT) : ℝ) ≤ Ktr * NT + 1 := hceilUpper.le
      have hceilBound : 2 * (Nat.ceil (Ktr * NT) : ℝ) + 1 ≤
          2 * Ktr * NT + 3 := by
        have htwice := mul_le_mul_of_nonneg_left hceilUpper' (by norm_num : 0 ≤ (2 : ℝ))
        nlinarith only [htwice]
      have hNTplusB : NT ≤ 5 * B := by
        calc
          NT = (n : ℝ) * T x := by rfl
          _ ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x := hNTplus2
          _ = 5 * B := by dsimp [B]; ring
      have hNTBound : 2 * Ktr * NT ≤ 10 * Ktr * B := by
        calc
          2 * Ktr * NT ≤ 2 * Ktr * (5 * B) :=
            mul_le_mul_of_nonneg_left hNTplusB (by positivity)
          _ = 10 * Ktr * B := by ring
      calc
        2 * (Nat.ceil (Ktr * NT) : ℝ) + 1 ≤ 2 * Ktr * NT + 3 := hceilBound
        _ ≤ 10 * Ktr * B + 3 := by
          simpa [add_comm] using (add_le_add_right hNTBound 3)
        _ ≤ (10 * Ktr + 3) * B := by
          calc
            10 * Ktr * B + 3 = 10 * Ktr * B + 3 * 1 := by ring
            _ ≤ 10 * Ktr * B + 3 * B := by
              simpa [add_comm] using
                (add_le_add_left
                  (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 3))
                  (10 * Ktr * B))
            _ = (10 * Ktr + 3) * B := by ring
        _ = (10 * Ktr + 3) * (L x) ^ ((52 : ℝ) / 100) * T x := by
          dsimp [B]
          ring
    have hHplus2coarse : ((H + 2 : ℕ) : ℝ) ≤
        (10 * Ktr + 4) * (L x) ^ 2 := by
      dsimp [H]
      push_cast
      have hceilUpper' : (Nat.ceil (Ktr * NT) : ℝ) ≤ Ktr * NT + 1 := hceilUpper.le
      have hceilBound : 2 * (Nat.ceil (Ktr * NT) : ℝ) + 2 ≤ 2 * Ktr * NT + 4 := by
        have htwice := mul_le_mul_of_nonneg_left hceilUpper' (by norm_num : 0 ≤ (2 : ℝ))
        nlinarith only [htwice]
      have hLsq : 1 ≤ (L x) ^ 2 := by
        exact one_le_pow₀ hL
      have hNTbound' : 2 * Ktr * NT ≤ 10 * Ktr * (L x) ^ 2 := by
        calc
          2 * Ktr * NT ≤ 2 * Ktr * (5 * (L x) ^ 2) :=
            mul_le_mul_of_nonneg_left hNTcoarse (by positivity)
          _ = 10 * Ktr * (L x) ^ 2 := by ring
      calc
        2 * (Nat.ceil (Ktr * NT) : ℝ) + 2 ≤ 2 * Ktr * NT + 4 := hceilBound
        _ ≤ 10 * Ktr * (L x) ^ 2 + 4 := by
          simpa [add_comm] using (add_le_add_right hNTbound' 4)
        _ ≤ (10 * Ktr + 4) * (L x) ^ 2 := by
          calc
            10 * Ktr * (L x) ^ 2 + 4 =
                10 * Ktr * (L x) ^ 2 + 4 * 1 := by ring
            _ ≤ 10 * Ktr * (L x) ^ 2 + 4 * (L x) ^ 2 := by gcongr
            _ = (10 * Ktr + 4) * (L x) ^ 2 := by ring
    have hHplus2Exp : ((H + 2 : ℕ) : ℝ) ≤ Real.exp y := by
      exact le_trans hHplus2coarse (by simpa [y, Real.rpow_natCast] using hDegreeExp)
    have hTpow52ge : 1 ≤ (L x) ^ ((52 : ℝ) / 100) * T x := hTtwo
    have hHdegreeLinear : ((H + 1 : ℕ) : ℝ) ≤
        (10 * Ktr + 3) * (L x) ^ ((52 : ℝ) / 100) * T x := hHdegUpper
    have hHplus2LinearCoarse : ((H + 2 : ℕ) : ℝ) ≤
        (10 * Ktr + 4) * (L x) ^ 2 := hHplus2coarse
    have hHplus2exp : ((H + 2 : ℕ) : ℝ) ≤ Real.exp y := hHplus2Exp
    have hNScale : NT ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x := hNTplus2
    have hNScaleCoarse : NT ≤ 5 * (L x) ^ 2 := hNTcoarse
    have hNTpositive : 0 < NT := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hNT4
    have hKtrFactor : 0 < 2 * Ktr * NT :=
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hKtr) hNTpositive
    have htailDegreePos : 0 < ((H + 1 : ℕ) : ℝ) := by
      exact lt_of_lt_of_le hKtrFactor hHdegLower
    have htailRatio :
        Real.exp 1 * lambdaTot / ((H + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      have hnum0 : 0 ≤ A + 2 * cLambda + 1 :=
        add_nonneg (add_nonneg hA.le
          (mul_nonneg (show (0 : ℝ) ≤ 2 from by norm_num) hcLambda.le))
          (show (0 : ℝ) ≤ 1 from by norm_num)
      have hfrac0 : 0 ≤ (A + 2 * cLambda + 1) / Real.log 2 :=
        div_nonneg hnum0 hlog2.le
      have hrest0 : 0 ≤ (A + 2 * cLambda + 1) / Real.log 2 + 1 :=
        add_nonneg hfrac0 (show (0 : ℝ) ≤ 1 from by norm_num)
      have hKfirst : Real.exp 1 * cLambda ≤ Ktr := by
        dsimp [Ktr]
        calc
          Real.exp 1 * cLambda ≤ Real.exp 1 * cLambda +
              ((A + 2 * cLambda + 1) / Real.log 2 + 1) := le_add_of_nonneg_right hrest0
          _ = Real.exp 1 * cLambda + (A + 2 * cLambda + 1) / Real.log 2 + 1 := by ring
      have hKnum : Real.exp 1 * cLambda * NT ≤ Ktr * NT :=
        mul_le_mul_of_nonneg_right hKfirst hNT0
      calc
        Real.exp 1 * lambdaTot / ((H + 1 : ℕ) : ℝ) =
            (Real.exp 1 * cLambda * NT) / ((H + 1 : ℕ) : ℝ) := by
              dsimp [lambdaTot]
              ring
        _ ≤ (Ktr * NT) / ((H + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hKnum htailDegreePos.le
        _ ≤ 1 / 2 := (div_le_iff₀ htailDegreePos).2 (by
          nlinarith only [hHdegLower])
    have htailSmall := factorial_tail_small_of_linear_degree hLambda0
      (H + 1) (Nat.succ_pos H) htailRatio
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hKlog : A + 2 * cLambda + 1 ≤ Ktr * Real.log 2 := by
      have hcancel := div_mul_cancel₀ (A + 2 * cLambda + 1) hlog2pos.ne'
      have hlogTerm : 0 ≤ (Real.exp 1 * cLambda + 1) * Real.log 2 :=
        mul_nonneg
          (add_nonneg (mul_nonneg (Real.exp_pos 1).le hcLambda.le)
            (show (0 : ℝ) ≤ 1 from by norm_num)) hlog2pos.le
      dsimp [Ktr]
      nlinarith only [hcancel, hlogTerm]
    have hntlog :
        (A + 2 * cLambda + 1) * NT ≤ ((H + 1 : ℕ) : ℝ) * Real.log 2 := by
      have hcoef : A + 2 * cLambda + 1 ≤ 2 * Ktr * Real.log 2 := by
        nlinarith only [hKlog, mul_nonneg hKtr.le hlog2pos.le]
      have hcoefNT := mul_le_mul_of_nonneg_right hcoef hNT0
      have hdegreeLog := mul_le_mul_of_nonneg_right hHdegLower hlog2pos.le
      nlinarith only [hcoefNT, hdegreeLog]
    have htailExp :
        lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ) ≤
          Real.exp (-A * NT - 2 * lambdaTot - 4) := by
      have hrate : Real.exp (-((H + 1 : ℕ) : ℝ) * Real.log 2) ≤
          Real.exp (-(A + 2 * cLambda + 1) * NT) :=
        Real.exp_le_exp.mpr (by nlinarith only [hntlog])
      have hrate2 : Real.exp (-(A + 2 * cLambda + 1) * NT) ≤
          Real.exp (-A * NT - 2 * lambdaTot - 4) := by
        apply Real.exp_le_exp.mpr
        dsimp [lambdaTot, cLambda]
        nlinarith only [hNT4]
      calc
        lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ) ≤ (1 / 2 : ℝ) ^ (H + 1) := htailSmall
        _ = Real.exp (-((H + 1 : ℕ) : ℝ) * Real.log 2) := one_half_pow_eq_exp (H + 1)
        _ ≤ Real.exp (-(A + 2 * cLambda + 1) * NT) := hrate
        _ ≤ Real.exp (-A * NT - 2 * lambdaTot - 4) := hrate2
    have hSigmaU : (∑ p ∈ U, (p.val : ℝ)) ≤ Real.exp (3 * y) := by
      have hUle : (∑ p ∈ U, (p.val : ℝ)) ≤
          (∑ p : P.GroupPrime, (p.val : ℝ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg U.subset_univ
          (by intro p hp hnot; positivity)
      calc
        (∑ p ∈ U, (p.val : ℝ)) ≤ (∑ p : P.GroupPrime, (p.val : ℝ)) := hUle
        _ = (∑ p ∈ P.allPrimes, (p : ℝ)) := groupPrime_sum_eq_allPrimes (fun p => (p : ℝ))
        _ ≤ 3 * (P.count : ℝ) * Real.exp (2 * y) := by
          simpa [y] using allPrimes_sum_le_exp_bound hP hL
        _ ≤ Real.exp y * Real.exp (2 * y) :=
          mul_le_mul_of_nonneg_right hprimeFactor (Real.exp_pos _).le
        _ = Real.exp (3 * y) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hSym := elementarySymmetric_two_range_sum_bound U y hY0 H hSigmaU
    have hSym0 : 0 ≤
        (∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k) +
          ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k := by
      apply add_nonneg
      · apply Finset.sum_nonneg
        intro k hk
        exact elementarySymmetric_nonneg (fun p : P.GroupPrime => (p.val : ℝ)) U k
          (fun p hp => by positivity)
      · apply Finset.sum_nonneg
        intro k hk
        exact elementarySymmetric_nonneg (fun p : P.GroupPrime => (p.val : ℝ)) U k
          (fun p hp => by positivity)
    have hHfactor : 2 * ((H + 2 : ℕ) : ℝ) ≤ Real.exp (2 * y) := by
      calc
        2 * ((H + 2 : ℕ) : ℝ) ≤ 2 * Real.exp y :=
          mul_le_mul_of_nonneg_left hHplus2exp (by norm_num)
        _ ≤ Real.exp y * Real.exp y :=
          mul_le_mul_of_nonneg_right hExpY2 (Real.exp_pos _).le
        _ = Real.exp (2 * y) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hSymExp :
        (∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k) +
          ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k ≤
        Real.exp (3 * ((H + 1 : ℕ) : ℝ) * y + 2 * y) := by
      calc
        _ ≤ 2 * ((H + 2 : ℕ) : ℝ) *
            Real.exp (((H + 1 : ℕ) : ℝ) * (3 * y)) := by
              simpa [Nat.cast_add] using hSym
        _ ≤ Real.exp (2 * y) *
            Real.exp (((H + 1 : ℕ) : ℝ) * (3 * y)) :=
              mul_le_mul_of_nonneg_right hHfactor (Real.exp_pos _).le
        _ = Real.exp (3 * ((H + 1 : ℕ) : ℝ) * y + 2 * y) := by
              rw [← Real.exp_add]
              congr 1 <;> ring
    have hXtwo : 2 ≤ X := le_trans hxPow hXlo
    have hInvLen := dyad_card_inv_le_exp_of_scale hxpos hXlo hXtwo
    have hM0 : 0 ≤ ((dyad X).card : ℝ)⁻¹ := by positivity
    have hQM : Q * (((dyad X).card : ℝ)⁻¹) ≤
        Real.exp ((Kactive : ℝ) * y) *
          (2 * Real.exp (-gamma * L x)) := by
      calc
        Q * ((dyad X).card : ℝ)⁻¹ ≤
            Real.exp ((Kactive : ℝ) * y) * ((dyad X).card : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hQ hM0
        _ ≤ Real.exp ((Kactive : ℝ) * y) * (2 * Real.exp (-gamma * L x)) :=
          mul_le_mul_of_nonneg_left hInvLen (Real.exp_pos _).le
    let Dval : ℝ := ((Kactive : ℝ) + 3 * ((H + 1 : ℕ) : ℝ) + 3) * y
    have hCRTscaled :
        Q * (((dyad X).card : ℝ)⁻¹ *
          ((∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k) +
            ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k)) ≤
          Real.exp (-gamma * L x + Dval) := by
      calc
        _ = (Q * ((dyad X).card : ℝ)⁻¹) *
            ((∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k) +
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k) := by ring
        _ ≤ (Real.exp ((Kactive : ℝ) * y) *
            (2 * Real.exp (-gamma * L x))) *
            ((∑ k ∈ Finset.range (H + 1), elementarySymmetric (fun p => (p.val : ℝ)) U k) +
              ∑ k ∈ Finset.range (H + 2), elementarySymmetric (fun p => (p.val : ℝ)) U k) :=
            mul_le_mul_of_nonneg_right hQM hSym0
        _ ≤ (Real.exp ((Kactive : ℝ) * y) *
            (2 * Real.exp (-gamma * L x))) *
            Real.exp (3 * ((H + 1 : ℕ) : ℝ) * y + 2 * y) :=
            mul_le_mul_of_nonneg_left hSymExp (by positivity)
        _ ≤ (Real.exp ((Kactive : ℝ) * y) *
            (Real.exp y * Real.exp (-gamma * L x))) *
            Real.exp (3 * ((H + 1 : ℕ) : ℝ) * y + 2 * y) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hExpY2 (Real.exp_pos _).le)
                (Real.exp_pos _).le)
              (Real.exp_pos _).le
        _ = Real.exp (-gamma * L x + Dval) := by
            calc
              _ = (Real.exp ((Kactive : ℝ) * y) * Real.exp y) *
                  (Real.exp (-gamma * L x) *
                    Real.exp (3 * ((H + 1 : ℕ) : ℝ) * y + 2 * y)) := by ring
              _ = Real.exp ((Kactive : ℝ) * y + y) *
                  Real.exp (-gamma * L x + (3 * ((H + 1 : ℕ) : ℝ) * y + 2 * y)) := by
                    rw [← Real.exp_add, ← Real.exp_add]
              _ = Real.exp (-gamma * L x + Dval) := by
                    rw [← Real.exp_add]
                    congr 1
                    dsimp [Dval]
                    push_cast
                    ring
    have hDcoef : ((Kactive : ℝ) + 3 * ((H + 1 : ℕ) : ℝ) + 3) ≤
        cCRT * (L x) ^ ((52 : ℝ) / 100) * T x := by
      have hbase : 1 ≤ (L x) ^ ((52 : ℝ) / 100) * T x := hTtwo
      calc
        _ ≤ cActive * (L x) ^ ((52 : ℝ) / 100) * T x +
            3 * ((10 * Ktr + 3) * (L x) ^ ((52 : ℝ) / 100) * T x) + 3 := by
              nlinarith only [hKactiveCast, hHdegreeLinear]
        _ ≤ cCRT * (L x) ^ ((52 : ℝ) / 100) * T x := by
              dsimp [cCRT]
              nlinarith only [hbase]
    have hDpow : (L x) ^ ((52 : ℝ) / 100) * (L x) ^ F.d / L x =
        ((L x) ^ delta)⁻¹ := by
      simpa [delta] using
        (L_rpow_052_mul_rpow_div_eq_inv (x := x) (d := F.d) hL)
    have hDupper : Dval / L x ≤ cCRT * (T x / (L x) ^ delta) := by
      calc
        Dval / L x ≤
            (cCRT * (L x) ^ ((52 : ℝ) / 100) * T x * y) / L x :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hDcoef hY0) (by linarith)
        _ = cCRT * (T x / (L x) ^ delta) := by
            rw [show y = (L x) ^ F.d by rfl]
            calc
              _ = cCRT * T x *
                  ((L x) ^ ((52 : ℝ) / 100) * (L x) ^ F.d / L x) := by ring
              _ = cCRT * (T x / (L x) ^ delta) := by rw [hDpow]; ring
    have hDsmall : Dval / L x < gamma / 4 := by
      calc
        Dval / L x ≤ cCRT * (T x / (L x) ^ delta) := hDupper
        _ < cCRT * (gamma / (4 * cCRT)) :=
          mul_lt_mul_of_pos_left hCRTsmall hcCRT
        _ = gamma / 4 := by field_simp [hcCRT.ne']
    have hDle : Dval ≤ (gamma / 4) * L x := by
      have h := (div_lt_iff₀ (by linarith : 0 < L x)).mp hDsmall
      exact le_of_lt h
    have hscaleUpper : NT ≤ 5 * (L x) ^ ((52 : ℝ) / 100) * T x := hNTplus2
    have hScaleCoef : A * NT + 2 * lambdaTot + 4 ≤ cScale *
        (L x) ^ ((52 : ℝ) / 100) * T x := by
      have hbase : 1 ≤ (L x) ^ ((52 : ℝ) / 100) * T x := hTtwo
      dsimp [lambdaTot, cLambda, cScale]
      calc
        _ ≤ 5 * (A + 2 * (4 * F.C₀ * F.vMax)) *
            (L x) ^ ((52 : ℝ) / 100) * T x + 4 := by
              have h := mul_le_mul_of_nonneg_left hscaleUpper
                (by positivity : 0 ≤ A + 2 * (4 * F.C₀ * F.vMax))
              nlinarith only [h]
        _ ≤ (5 * (A + 2 * (4 * F.C₀ * F.vMax)) + 4) *
            (L x) ^ ((52 : ℝ) / 100) * T x := by nlinarith only [hbase]
    have hpowRatio : ((L x) ^ ((52 : ℝ) / 100) * T x) / L x =
        T x / (L x) ^ ((48 : ℝ) / 100) := by
      have hpow := L_rpow_052_mul_rpow_div_eq_inv (x := x) (d := 0) hL
      have hpow' : (L x) ^ ((52 : ℝ) / 100) / L x =
          ((L x) ^ ((48 : ℝ) / 100))⁻¹ := by simpa using hpow
      calc
        ((L x) ^ ((52 : ℝ) / 100) * T x) / L x =
            T x * ((L x) ^ ((52 : ℝ) / 100) / L x) := by ring
        _ = T x * ((L x) ^ ((48 : ℝ) / 100))⁻¹ := by rw [hpow']
        _ = T x / (L x) ^ ((48 : ℝ) / 100) := by ring
    have hScaleOver : (A * NT + 2 * lambdaTot + 4) / L x ≤
        cScale * (T x / (L x) ^ ((48 : ℝ) / 100)) := by
      calc
        _ ≤ (cScale * (L x) ^ ((52 : ℝ) / 100) * T x) / L x :=
          div_le_div_of_nonneg_right hScaleCoef (by positivity)
        _ = cScale * (((L x) ^ ((52 : ℝ) / 100) * T x) / L x) := by ring
        _ = _ := by rw [hpowRatio]
    have hScaleSmall : (A * NT + 2 * lambdaTot + 4) / L x < gamma / 4 := by
      calc
        _ ≤ cScale * (T x / (L x) ^ ((48 : ℝ) / 100)) := hScaleOver
        _ < cScale * (gamma / (4 * cScale)) :=
          mul_lt_mul_of_pos_left hScalesmall hcScale
        _ = gamma / 4 := by field_simp [hcScale.ne']
    have hScaleLe : A * NT + 2 * lambdaTot + 4 ≤ (gamma / 4) * L x := by
      have h := (div_lt_iff₀ (by linarith : 0 < L x)).mp hScaleSmall
      exact le_of_lt h
    have hCRTtarget : -gamma * L x + Dval ≤ -A * NT - 2 * lambdaTot - 4 := by
      have hγL0 : 0 ≤ gamma * L x := mul_nonneg hgamma.le (by linarith [hL])
      nlinarith only [hDle, hScaleLe, hγL0]
    have hCRTexp : Real.exp (-gamma * L x + Dval) ≤
        Real.exp (-A * NT - 2 * lambdaTot - 4) :=
      Real.exp_le_exp.mpr hCRTtarget

    let sumLow : ℝ :=
      ∑ k ∈ Finset.range (H + 1),
        elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ)) U k
    let sumHigh : ℝ :=
      ∑ k ∈ Finset.range (H + 2),
        elementarySymmetric (fun p : P.GroupPrime => (p.val : ℝ)) U k
    let errCRT : ℝ := ((dyad X).card : ℝ)⁻¹ * sumLow +
      ((dyad X).card : ℝ)⁻¹ * sumHigh
    let tail : ℝ := lambdaTot ^ (H + 1) / ((H + 1).factorial : ℝ)
    let missProd : ℝ := ∏ p ∈ U, (1 - residueMissMean n q h p)
    have hprodBase := inactiveMissProduct_lower n q h active hmu0 hmuHalf
    have hprod : Real.exp (-2 * lambdaTot) ≤ missProd := by
      calc
        Real.exp (-2 * lambdaTot) ≤
            Real.exp (-2 * ∑ p ∈ U, residueMissMean n q h p) := by
              apply Real.exp_le_exp.mpr
              nlinarith only [hmuSum]
        _ ≤ missProd := by simpa [missProd] using hprodBase
    have hCRT : Q * errCRT ≤ Real.exp (-A * NT - 2 * lambdaTot - 4) := by
      calc
        Q * errCRT = Q * (((dyad X).card : ℝ)⁻¹ * (sumLow + sumHigh)) := by
          dsimp [errCRT]
          ring
        _ ≤ Real.exp (-gamma * L x + Dval) := by
          simpa [sumLow, sumHigh] using hCRTscaled
        _ ≤ Real.exp (-A * NT - 2 * lambdaTot - 4) := hCRTexp
    have hTail : tail ≤ Real.exp (-A * NT - 2 * lambdaTot - 4) := by
      simpa [tail] using htailExp
    have hbudget := scaled_errors_to_relative_budget
      (A := A) (S := NT) (lambdaTot := lambdaTot) (Q := Q)
      (errCRT := errCRT) (tail := tail) (prod := missProd)
      hQpos hprod hCRT hTail
    have herrorBudget :
        ((dyad X).card : ℝ)⁻¹ * sumLow +
          ((dyad X).card : ℝ)⁻¹ * sumHigh + Q⁻¹ * tail ≤
        Real.exp (-A * NT) * Q⁻¹ * missProd := by
      calc
        _ = errCRT + Q⁻¹ * tail := by dsimp [errCRT]
        _ ≤ Real.exp (-A * NT) * (Q⁻¹ * missProd) := hbudget
        _ = Real.exp (-A * NT) * Q⁻¹ * missProd := by ring
    have hXceiltwo : X ≤ 2 * X := by linarith [hXlo]
    let lo : ℤ := ⌈X⌉
    let hi : ℤ := ⌈2 * X⌉
    have hlohi : lo ≤ hi := by
      dsimp [lo, hi]
      exact Int.ceil_le_ceil hXceiltwo
    have hcardDyad : 0 < (dyad X).card := by
      have hcardReal : (0 : ℝ) < ((dyad X).card : ℝ) := by
        have hcardLower := dyad_card_real_lower_of_two_le hXtwo
        linarith [hcardLower]
      exact_mod_cast hcardReal
    have hcard : 0 < (Finset.Ico lo hi).card := by
      simpa [lo, hi, dyad] using hcardDyad
    have hExpAssoc : Real.exp (-A * NT) = Real.exp (-A * (N x : ℝ) * T x) := by
      congr 1
      dsimp [NT, n]
      ring
    have heps : 0 ≤ Real.exp (-A * NT) := (Real.exp_pos _).le
    have hbudgetFinal :
        ((Finset.Ico lo hi).card : ℝ)⁻¹ * sumLow +
          ((Finset.Ico lo hi).card : ℝ)⁻¹ * sumHigh + Q⁻¹ * tail ≤
        Real.exp (-A * NT) * Q⁻¹ * missProd := by
      simpa [lo, hi, dyad] using herrorBudget
    have hepsTarget : 0 ≤ Real.exp (-A * (N x : ℝ) * T x) := (Real.exp_pos _).le
    have hbudgetTarget :
        ((Finset.Ico lo hi).card : ℝ)⁻¹ * sumLow +
          ((Finset.Ico lo hi).card : ℝ)⁻¹ * sumHigh + Q⁻¹ * tail ≤
        Real.exp (-A * (N x : ℝ) * T x) * Q⁻¹ * missProd := by
      rw [← hExpAssoc]
      simpa [lo, hi, dyad] using herrorBudget
    exact uniform_residue_replacement_of_error_budget
      (P := P) n q h hq active hmu lambdaTot hLambda0 hmuSum
      lo hi hlohi hcard H hHeven (Real.exp (-A * (N x : ℝ) * T x))
      hepsTarget hbudgetTarget

example : Erdos821.Blueprint.Graph.uniform_residue_replacement_statement :=
  @Erdos821.P3Core.uniform_residue_replacement_proof

end Erdos821.P3Core

