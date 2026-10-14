import Erdos821.Blueprint.Graph

noncomputable section
open scoped BigOperators
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Core

open Erdos821.Blueprint.Graph

lemma omegaGroup_ge_of_physical {P : PrimeGroups} {M : ℕ} (n : ℤ)
    (a : P.Labels M) (ha : P.physical M n a) (g : P.Group) :
    M ≤ P.omegaGroup g n := by
  classical
  let S : Finset ℕ := Finset.univ.image fun i : Fin M => (a g i).val
  have hsub : S ⊆ (P.primes g).filter (fun p => (p : ℤ) ∣ n) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact Finset.mem_filter.mpr ⟨(a g i).property, (ha g).2 i⟩
  have hinj : Function.Injective fun i : Fin M => (a g i).val := by
    intro i j hij
    exact (ha g).1 (Subtype.ext hij)
  have hcard : S.card = M := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  calc
    M = S.card := hcard.symm
    _ ≤ ((P.primes g).filter (fun p : ℕ => (p : ℤ) ∣ n)).card :=
      Finset.card_le_card hsub
    _ = P.omegaGroup g n := by rfl

lemma omega_ge_card_mul_of_physical {P : PrimeGroups} {M : ℕ} (n : ℤ)
    (a : P.Labels M) (ha : P.physical M n a) :
    M * P.count ≤ P.omega n := by
  classical
  calc
    M * P.count = ∑ _g : P.Group, M := by simp [Nat.mul_comm]
    _ ≤ ∑ g : P.Group, P.omegaGroup g n :=
      Finset.sum_le_sum fun g hg => omegaGroup_ge_of_physical n a ha g
    _ = P.omega n := rfl

lemma damping_le_one_of_physical {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (n : ℤ) (a : P.Labels (J + F.ell))
    (ha : P.physical (J + F.ell) n a) : A.damping n ≤ 1 := by
  have homega : ((J + F.ell) * P.count : ℝ) ≤ (P.omega n : ℝ) := by
    exact_mod_cast omega_ge_card_mul_of_physical n a ha
  have he : 0 ≤ ((P.omega n : ℝ) - (J + F.ell) * P.count) / 2 := by
    linarith
  change F.q ^ (((P.omega n : ℝ) - (J + F.ell) * P.count) / 2) ≤ 1
  exact Real.rpow_le_one F.q_pos.le F.q_lt.le he

lemma V_pos_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (g : P.Group) : 0 < P.V g := by
  rcases hP with ⟨_, _, _, _, hV, _⟩
  exact lt_of_lt_of_le F.vMin_pos (hV g).1

lemma V_lower_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (g : P.Group) : F.vMin ≤ P.V g := by
  rcases hP with ⟨_, _, _, _, hV, _⟩
  exact (hV g).1

lemma mu_pos_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (g : P.Group) (p : P.Prime g) : 0 < P.mu g p := by
  have hp : 0 < (p.val : ℝ) := by
    exact_mod_cast (P.prime g p.val p.property).pos
  simp only [PrimeGroups.mu]
  exact inv_pos.mpr (mul_pos (V_pos_of_admissible hP g) hp)

lemma auxMass_pos_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    {J m : ℕ} (ν : Pattern P J F.ell m) (u : P.Aux J)
    (hP : P.Admissible F x) : 0 < ν.auxMass u := by
  classical
  dsimp [Pattern.auxMass]
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact mu_pos_of_admissible hP g (u g i)

lemma physicalTargetMass_pos_of_admissible {P : PrimeGroups}
    {J ell m : ℕ} (ν : Pattern P J ell m) (hP : ∀ g : P.Group, 0 < P.V g) :
    0 < ν.physicalTargetMass := by
  classical
  dsimp [Pattern.physicalTargetMass]
  apply Finset.prod_pos
  intro g hg
  exact zpow_pos (hP g) _

lemma damping_pos {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℤ) : 0 < A.damping n :=
  Real.rpow_pos_of_pos F.q_pos _

lemma damping_eq_group_product_of_physical {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (n : ℤ) (a : P.Labels (J + F.ell))
    (ha : P.physical (J + F.ell) n a) :
    A.damping n = ∏ g : P.Group,
      F.q ^ (((P.omegaGroup g n - (J + F.ell) : ℕ) : ℝ) / 2) := by
  have hM : ∀ g : P.Group, J + F.ell ≤ P.omegaGroup g n :=
    fun g => omegaGroup_ge_of_physical n a ha g
  have hOmega : (P.omega n : ℝ) = ∑ g : P.Group, (P.omegaGroup g n : ℝ) := by
    rw [PrimeGroups.omega, Nat.cast_sum]
  have hMsum : ((J + F.ell : ℕ) : ℝ) * (P.count : ℝ) =
      ∑ _g : P.Group, ((J + F.ell : ℕ) : ℝ) := by
    simp [Nat.cast_add, mul_comm]
    ring
  have hexp :
      ((P.omega n : ℝ) - ((J + F.ell) * P.count : ℝ)) / 2 =
        ∑ g : P.Group, ((P.omegaGroup g n : ℝ) - (J + F.ell : ℝ)) / 2 := by
    rw [hOmega]
    have hMsum' : ((J : ℝ) + (F.ell : ℝ)) * (P.count : ℝ) =
        ∑ _g : P.Group, ((J : ℝ) + (F.ell : ℝ)) := by
      simpa only [Nat.cast_add] using hMsum
    rw [hMsum', ← Finset.sum_sub_distrib, ← Finset.sum_div]
  change F.q ^ (((P.omega n : ℝ) - (J + F.ell) * P.count) / 2) = _
  rw [hexp, Real.rpow_sum_of_pos F.q_pos]
  apply Finset.prod_congr rfl
  intro g hg
  rw [Nat.cast_sub (hM g)]
  simp [Nat.cast_add]

lemma shifted_polynomial_geometric_bound (q : ℝ) (hq : 0 < q) (hq' : q < 1)
    (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ,
      ((z + K : ℕ) : ℝ) ^ K * q ^ ((z : ℝ) / 2) ≤ C := by
  let r : ℝ := Real.sqrt q
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hr1 : r < 1 := by
    dsimp [r]
    have hs := Real.sq_sqrt hq.le
    nlinarith
  have hqpow (z : ℕ) : q ^ ((z : ℝ) / 2) = r ^ z := by
    rw [Real.rpow_div_two_eq_sqrt (z : ℝ) hq.le]
    dsimp [r]
    exact Real.rpow_natCast (Real.sqrt q) z
  have hbase : Tendsto (fun z : ℕ => (z : ℝ) ^ K * r ^ z) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one K hr0 hr1
  let c : ℝ := ((K : ℝ) + 1) ^ K
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hscaled : Tendsto (fun z : ℕ => c * ((z : ℝ) ^ K * r ^ z)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hbase)
  have hev : ∀ᶠ z : ℕ in atTop, c * ((z : ℝ) ^ K * r ^ z) < 1 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.1 hev
  let Z₀ := max Z 1
  have hlate : ∀ z : ℕ, Z₀ ≤ z →
      ((z + K : ℕ) : ℝ) ^ K * r ^ z < 1 := by
    intro z hz
    have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (le_trans (le_max_right Z 1) hz)
    have hlin : (z : ℝ) + (K : ℝ) ≤ ((K : ℝ) + 1) * z := by
      nlinarith
    have hpoly : ((z + K : ℕ) : ℝ) ^ K ≤ c * (z : ℝ) ^ K := by
      calc
        ((z + K : ℕ) : ℝ) ^ K = ((z : ℝ) + (K : ℝ)) ^ K := by norm_cast
        _ ≤ (((K : ℝ) + 1) * z) ^ K :=
          pow_le_pow_left₀ (by positivity) hlin K
        _ = c * (z : ℝ) ^ K := by
          dsimp [c]
          rw [mul_pow]
    calc
      ((z + K : ℕ) : ℝ) ^ K * r ^ z ≤ c * ((z : ℝ) ^ K * r ^ z) := by
        calc
          ((z + K : ℕ) : ℝ) ^ K * r ^ z ≤ (c * (z : ℝ) ^ K) * r ^ z :=
            mul_le_mul_of_nonneg_right hpoly (pow_nonneg hr0 _)
          _ = c * ((z : ℝ) ^ K * r ^ z) := by ring
      _ < 1 := hZ z (le_trans (le_max_left Z 1) hz)
  let C : ℝ := (∑ z ∈ Finset.range Z₀, |((z + K : ℕ) : ℝ) ^ K * r ^ z|) + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have hsum : 0 ≤ ∑ z ∈ Finset.range Z₀,
        |((z + K : ℕ) : ℝ) ^ K * r ^ z| := Finset.sum_nonneg fun z hz => abs_nonneg _
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro z
  rw [hqpow z]
  by_cases hz : Z₀ ≤ z
  · have hnonneg : 0 ≤ ((z + K : ℕ) : ℝ) ^ K * r ^ z := by positivity
    have hlt := hlate z hz
    dsimp [C]
    have hsum : 0 ≤ ∑ n ∈ Finset.range Z₀,
        |((n + K : ℕ) : ℝ) ^ K * r ^ n| := Finset.sum_nonneg fun n hn => abs_nonneg _
    linarith
  · have hzlt : z < Z₀ := Nat.lt_of_not_ge hz
    have hnonneg : 0 ≤ ((z + K : ℕ) : ℝ) ^ K * r ^ z := by positivity
    have hsingle : |((z + K : ℕ) : ℝ) ^ K * r ^ z| ≤
        ∑ n ∈ Finset.range Z₀, |((n + K : ℕ) : ℝ) ^ K * r ^ n| := by
      exact Finset.single_le_sum (s := Finset.range Z₀)
        (f := fun n => |((n + K : ℕ) : ℝ) ^ K * r ^ n|)
        (fun n hn => abs_nonneg _) (Finset.mem_range.mpr hzlt)
    dsimp [C]
    calc
      ((z + K : ℕ) : ℝ) ^ K * r ^ z =
          |((z + K : ℕ) : ℝ) ^ K * r ^ z| := (abs_of_nonneg hnonneg).symm
      _ ≤ ∑ n ∈ Finset.range Z₀, |((n + K : ℕ) : ℝ) ^ K * r ^ n| := hsingle
      _ ≤ (∑ n ∈ Finset.range Z₀, |((n + K : ℕ) : ℝ) ^ K * r ^ n|) + 1 := by
        have hs : 0 ≤ ∑ n ∈ Finset.range Z₀,
            |((n + K : ℕ) : ℝ) ^ K * r ^ n| := Finset.sum_nonneg fun n hn => abs_nonneg _
        linarith

lemma negative_power_le_max_pow {vMin V : ℝ} (hv : 0 < vMin) (hV : vMin ≤ V)
    (t K : ℕ) (ht : t ≤ K) :
    V ^ (-(t : ℤ)) ≤ (max 1 vMin⁻¹) ^ K := by
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  have hInv : V⁻¹ ≤ vMin⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hv hV
  have hbase : V⁻¹ ≤ max 1 vMin⁻¹ := le_trans hInv (le_max_right _ _)
  have hbase0 : 0 ≤ V⁻¹ := inv_nonneg.mpr hVpos.le
  calc
    V ^ (-(t : ℤ)) = (V⁻¹) ^ t := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    _ ≤ (max 1 vMin⁻¹) ^ t := pow_le_pow_left₀ hbase0 hbase t
    _ ≤ (max 1 vMin⁻¹) ^ K := pow_le_pow_right₀ (le_max_left _ _) ht

lemma damped_polynomial_factor_bound (q vMin : ℝ) (hq : 0 < q) (hq' : q < 1)
    (hv : 0 < vMin) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z t : ℕ) (V : ℝ), t ≤ K → vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + K : ℕ) : ℝ) ^ K * q ^ ((z : ℝ) / 2) ≤ C := by
  obtain ⟨Cq, hCq, hqbound⟩ := shifted_polynomial_geometric_bound q hq hq' K
  let Cv : ℝ := (max 1 vMin⁻¹) ^ K
  have hCv : 0 < Cv := by
    dsimp [Cv]
    exact pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨Cv * Cq, mul_pos hCv hCq, ?_⟩
  intro z t V ht hV
  have hVbound : V ^ (-(t : ℤ)) ≤ Cv := by
    simpa [Cv] using negative_power_le_max_pow hv hV t K ht
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  have hVnonneg : 0 ≤ V ^ (-(t : ℤ)) := (zpow_pos hVpos _).le
  have hpoly_nonneg : 0 ≤ ((z + K : ℕ) : ℝ) ^ K * q ^ ((z : ℝ) / 2) := by
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg hq.le _)
  have hpoly_bound : ((z + K : ℕ) : ℝ) ^ K * q ^ ((z : ℝ) / 2) ≤ Cq :=
    hqbound z
  calc
    V ^ (-(t : ℤ)) * ((z + K : ℕ) : ℝ) ^ K * q ^ ((z : ℝ) / 2) =
        V ^ (-(t : ℤ)) * (((z + K : ℕ) : ℝ) ^ K * q ^ ((z : ℝ) / 2)) := by ring
    _ ≤ Cv * Cq := mul_le_mul hVbound hpoly_bound hpoly_nonneg hCv.le

lemma sum_reciprocal_primes_subtype (P : PrimeGroups) (g : P.Group) :
    (∑ p : P.Prime g, (p.val : ℝ)⁻¹) = P.V g := by
  classical
  simpa only [PrimeGroups.Prime, PrimeGroups.V, Finset.univ_eq_attach] using
    (Finset.sum_attach (P.primes g) fun p : ℕ => (p : ℝ)⁻¹)

lemma sum_mu_eq_one (P : PrimeGroups) (g : P.Group) (hV : P.V g ≠ 0) :
    (∑ p : P.Prime g, P.mu g p) = 1 := by
  classical
  change (∑ p : P.Prime g, (P.V g * (p.val : ℝ))⁻¹) = 1
  calc
    (∑ p : P.Prime g, (P.V g * (p.val : ℝ))⁻¹) =
        (P.V g)⁻¹ * ∑ p : P.Prime g, (p.val : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p.val : ℝ) ≠ 0 := by
        exact_mod_cast (P.prime g p.val p.property).ne_zero
      field_simp [hV, hp0]
    _ = (P.V g)⁻¹ * P.V g := by rw [sum_reciprocal_primes_subtype]
    _ = 1 := inv_mul_cancel₀ hV

lemma sum_auxiliary_mass_eq_one (P : PrimeGroups) (J : ℕ)
    (hV : ∀ g : P.Group, P.V g ≠ 0) :
    (∑ u : P.Aux J, ∏ g, ∏ i, P.mu g (u g i)) = 1 := by
  classical
  have hgroup (g : P.Group) :
      (∑ u : Fin J → P.Prime g, ∏ i, P.mu g (u i)) = 1 := by
    calc
      (∑ u : Fin J → P.Prime g, ∏ i, P.mu g (u i)) =
          (∑ p : P.Prime g, P.mu g p) ^ J := (Fintype.sum_pow _ _).symm
      _ = 1 := by rw [sum_mu_eq_one P g (hV g)]; simp
  change (∑ u : ∀ g : P.Group, Fin J → P.Prime g, ∏ g, ∏ i, P.mu g (u g i)) = 1
  rw [← Fintype.prod_sum
    (fun g : P.Group => fun u : Fin J → P.Prime g => ∏ i, P.mu g (u i))]
  calc
    ∏ g : P.Group, (∑ u : Fin J → P.Prime g, ∏ i, P.mu g (u i)) =
        ∏ _g : P.Group, (1 : ℝ) := by
          apply Finset.prod_congr rfl
          intro g hg
          exact hgroup g
    _ = 1 := by simp

lemma tsum_supported_on_single_position {α : Type*} [Fintype α] (n₀ : ℤ)
    (f : ℤ × α → ℝ) (hf : ∀ z, z.1 ≠ n₀ → f z = 0) :
    (∑' z : ℤ × α, f z) = ∑ a : α, f (n₀, a) := by
  classical
  let S : Finset (ℤ × α) := Finset.univ.image fun a : α => (n₀, a)
  have hinj : Set.InjOn (fun a : α => (n₀, a)) (Finset.univ : Finset α) := by
    intro a ha b hb hab
    exact (Prod.mk.inj hab).2
  rw [tsum_eq_sum (s := S)]
  · calc
      (∑ z ∈ S, f z) = ∑ a ∈ Finset.univ, f (n₀, a) := by
        dsimp [S]
        exact Finset.sum_image hinj
      _ = ∑ a : α, f (n₀, a) := by simp
  · intro z hz
    by_cases hpos : z.1 = n₀
    · have hmem : z ∈ S := by
        apply Finset.mem_image.mpr
        exact ⟨z.2, Finset.mem_univ _, Prod.ext hpos.symm rfl⟩
      exact (hz hmem).elim
    · exact hf z hpos

lemma finset_sum_supported_at_position {α : Type*} [Fintype α]
    (S : Finset (ℤ × α)) (n₀ : ℤ) (f : ℤ × α → ℝ)
    (hlabels : ∀ a, (n₀, a) ∈ S)
    (hzero : ∀ z ∈ S, z.1 ≠ n₀ → f z = 0) :
    (∑ z ∈ S, f z) = ∑ a : α, f (n₀, a) := by
  classical
  let T : Finset (ℤ × α) := Finset.univ.image fun a : α => (n₀, a)
  have hTsub : T ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    exact hlabels a
  have hzero' : ∀ z ∈ S, z ∉ T → f z = 0 := by
    intro z hzS hzT
    apply hzero z hzS
    intro hpos
    apply hzT
    apply Finset.mem_image.mpr
    exact ⟨z.2, Finset.mem_univ _, Prod.ext hpos.symm rfl⟩
  calc
    (∑ z ∈ S, f z) = ∑ z ∈ T, f z := (Finset.sum_subset hTsub hzero').symm
    _ = ∑ a ∈ Finset.univ, f (n₀, a) := by
      dsimp [T]
      exact Finset.sum_image (by
        intro a ha b hb hab
        exact (Prod.mk.inj hab).2)
    _ = ∑ a : α, f (n₀, a) := by simp

lemma patternMass_nonneg {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) : 0 ≤ A.patternMass := by
  classical
  unfold Model.patternMass
  apply Finset.sum_nonneg
  intro v hv
  apply Real.sSup_nonneg
  intro r hr
  rcases hr with ⟨z, rfl⟩
  exact norm_nonneg _

lemma norm_imaginaryPower (n : ℕ) (ζ : ℝ) : ‖imaginaryPower n ζ‖ = 1 := by
  unfold imaginaryPower
  rw [Complex.norm_exp]
  have hre : (ζ * Real.log n * Complex.I).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add]
  rw [hre, Real.exp_zero]

def possiblePhysicalPositions {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℤ) : Finset ℤ :=
  Finset.univ.image fun w : Fin A.patternCount × (A.Labels × P.Aux J) =>
    n + A.k * ((A.pattern w.1).D w.2.1 w.2.2 : ℤ)

def possiblePhysicalTargets {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℤ) : Finset A.State :=
  (possiblePhysicalPositions A n).product Finset.univ

lemma physicalRaw_zero_outside_targets {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℤ) (a : A.Labels) (z' : A.State)
    (hz' : z' ∉ possiblePhysicalTargets A n) :
    A.physicalRaw true (n, a) z' = 0 := by
  classical
  have hpos (v : Fin A.patternCount) (u : P.Aux J) :
      z'.1 ≠ n + A.k * ((A.pattern v).D a u : ℤ) := by
    intro h
    apply hz'
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨(v, (a, u)), Finset.mem_univ _, h.symm⟩
    · exact Finset.mem_univ _
  simp [Model.physicalRaw, hpos]

def labelsActEquiv {P : PrimeGroups} {M : ℕ} (π : P.Permutations M) :
    P.Labels M ≃ P.Labels M where
  toFun := P.act π
  invFun := P.act (fun g => (π g).symm)
  left_inv := by
    intro a
    funext g i
    simp [PrimeGroups.act]
  right_inv := by
    intro a
    funext g i
    simp [PrimeGroups.act]

lemma physical_act {P : PrimeGroups} {M : ℕ} (π : P.Permutations M)
    (n : ℤ) (a : P.Labels M) (ha : P.physical M n a) :
    P.physical M n (P.act π a) := by
  intro g
  refine ⟨?_, ?_⟩
  · intro i j hij
    have h : a g (π g i) = a g (π g j) := by simpa [PrimeGroups.act] using hij
    exact (π g).injective ((ha g).1 h)
  · intro i
    exact (ha g).2 (π g i)

lemma physical_act_iff {P : PrimeGroups} {M : ℕ} (π : P.Permutations M)
    (n : ℤ) (a : P.Labels M) :
    P.physical M n (P.act π a) ↔ P.physical M n a := by
  constructor
  · intro h
    have h' := physical_act (fun g => (π g).symm) n (P.act π a) h
    have hlabels : P.act (fun g => (π g).symm) (P.act π a) = a := by
      funext g i
      simp [PrimeGroups.act, Equiv.symm_apply_apply]
    simpa [hlabels] using h'
  · exact physical_act π n a

lemma sum_possibleTargets_act {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℤ) (π : P.Permutations (J + F.ell))
    (f : A.State → ℝ) :
    (∑ z' ∈ possiblePhysicalTargets A n, f (z'.1, P.act π z'.2)) =
      ∑ z' ∈ possiblePhysicalTargets A n, f z' := by
  classical
  change (∑ z' ∈ possiblePhysicalPositions A n ×ˢ Finset.univ,
      f (z'.1, P.act π z'.2)) =
    ∑ z' ∈ possiblePhysicalPositions A n ×ˢ Finset.univ, f z'
  rw [Finset.sum_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n' hn'
  exact Equiv.sum_comp (labelsActEquiv π) (fun b => f (n', b))

lemma physicalKernel_zero_outside_targets {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℤ) (a : A.Labels) (z' : A.State)
    (hz' : z' ∉ possiblePhysicalTargets A n) :
    A.physicalKernel true (n, a) z' = 0 := by
  classical
  have hpos (π : P.Permutations (J + F.ell)) (v : Fin A.patternCount)
      (u : P.Aux J) :
      z'.1 ≠ n + A.k * ((A.pattern v).D (P.act π a) u : ℤ) := by
    intro h
    apply hz'
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨(v, (P.act π a, u)), Finset.mem_univ _, ?_⟩
      exact h.symm
    · exact Finset.mem_univ _
  simp [Model.physicalKernel, Model.physicalRaw, hpos]

lemma tsum_norm_finite_average {α ι : Type*} [Fintype ι]
    (S : Finset α) (c : ℂ) (K : ι → α → ℂ)
    (hsupp : ∀ i a, a ∉ S → K i a = 0) :
    (∑' a, ‖c * ∑ i, K i a‖) ≤
      ‖c‖ * ∑ i, ∑ a ∈ S, ‖K i a‖ := by
  classical
  rw [tsum_eq_sum (s := S) (by
    intro a ha
    have hzero : ∀ i, K i a = 0 := fun i => hsupp i a ha
    simp [hzero])]
  calc
    (∑ a ∈ S, ‖c * ∑ i, K i a‖) ≤
        ∑ a ∈ S, ‖c‖ * ∑ i, ‖K i a‖ := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        ‖c * ∑ i, K i a‖ = ‖c‖ * ‖∑ i, K i a‖ := norm_mul _ _
        _ ≤ ‖c‖ * ∑ i, ‖K i a‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ∑ a ∈ S, ∑ i, ‖c‖ * ‖K i a‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ a ∈ S, ‖c‖ * ‖K i a‖ := by rw [Finset.sum_comm]
    _ = ‖c‖ * ∑ i, ∑ a ∈ S, ‖K i a‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

lemma coefficient_norm_le_patternMass {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (v : Fin A.patternCount)
    (a b : A.BigLabels) (u : P.BigAux J) :
    ‖(A.pattern v).coefficient a b u‖ ≤ A.patternMass := by
  classical
  let cfun : A.BigLabels × A.BigLabels × P.BigAux J → ℝ := fun z =>
    ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖
  have hbdd : BddAbove (Set.range cfun) := (Set.finite_range cfun).bddAbove
  have hsup : ‖(A.pattern v).coefficient a b u‖ ≤ sSup (Set.range cfun) := by
    apply le_csSup hbdd
    exact ⟨(a, b, u), rfl⟩
  have hnonneg (w : Fin A.patternCount) :
      0 ≤ sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
        ‖(A.pattern w).coefficient z.1 z.2.1 z.2.2‖)) := by
    let cf : A.BigLabels × A.BigLabels × P.BigAux J → ℝ := fun z =>
      ‖(A.pattern w).coefficient z.1 z.2.1 z.2.2‖
    have hbdd' : BddAbove (Set.range cf) := (Set.finite_range cf).bddAbove
    have hmem : cf (a, b, u) ∈ Set.range cf := ⟨(a, b, u), rfl⟩
    exact (norm_nonneg _).trans (le_csSup hbdd' hmem)
  calc
    ‖(A.pattern v).coefficient a b u‖ ≤ sSup (Set.range cfun) := hsup
    _ ≤ ∑ w : Fin A.patternCount, sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
          ‖(A.pattern w).coefficient z.1 z.2.1 z.2.2‖)) := by
      exact Finset.single_le_sum (fun w hw => hnonneg w) (Finset.mem_univ v)
    _ = A.patternMass := rfl

lemma coefficient_norm_le_patternSup {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (v : Fin A.patternCount)
    (a b : A.BigLabels) (u : P.BigAux J) :
    ‖(A.pattern v).coefficient a b u‖ ≤
      sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
        ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) := by
  classical
  let cfun : A.BigLabels × A.BigLabels × P.BigAux J → ℝ := fun z =>
    ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖
  have hbdd : BddAbove (Set.range cfun) := (Set.finite_range cfun).bddAbove
  apply le_csSup hbdd
  exact ⟨(a, b, u), rfl⟩

lemma nonshared_slot_count_le {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (g : P.Group) :
    (Finset.univ.filter (fun i : Fin (J + ell) => ¬ ν.shared g i)).card ≤ ell + m := by
  classical
  let sharedWitnesses : Finset (Fin (J + ell)) :=
    (Finset.univ \ ν.changed g).image ν.slot
  let freeSlots : Finset (Fin (J + ell)) :=
    Finset.univ.filter (fun i : Fin (J + ell) => ¬ ν.shared g i)
  have hslot : Function.Injective ν.slot := by
    intro i j hij
    apply Fin.ext
    simpa [Pattern.slot] using congrArg Fin.val hij
  have hcardShared : sharedWitnesses.card = J - (ν.changed g).card := by
    dsimp [sharedWitnesses]
    rw [Finset.card_image_of_injective _ hslot,
      Finset.card_sdiff_of_subset (Finset.subset_univ (ν.changed g))]
    simp
  have hshared : ∀ i ∈ sharedWitnesses, ν.shared g i := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact ⟨j, rfl, (Finset.mem_sdiff.mp hj).2⟩
  have hfree_subset : freeSlots ⊆ Finset.univ \ sharedWitnesses := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hish
    exact (Finset.mem_filter.mp hi).2 (hshared i hish)
  have hfree_card : freeSlots.card ≤ ell + (ν.changed g).card := by
    calc
      freeSlots.card ≤ (Finset.univ \ sharedWitnesses).card := Finset.card_le_card hfree_subset
      _ = (J + ell) - (J - (ν.changed g).card) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ sharedWitnesses), hcardShared]
        simp
      _ = ell + (ν.changed g).card := by
        have hchangedJ : (ν.changed g).card ≤ J := by
          simpa using (Finset.card_le_card (Finset.subset_univ (ν.changed g)))
        omega
  have hchanged := ν.bound g
  simpa [freeSlots] using hfree_card.trans (Nat.add_le_add_left hchanged ell)

lemma omegaGroup_ge_of_injective_dividing {P : PrimeGroups} {M : ℕ} (g : P.Group)
    (n : ℤ) (a : Fin M → P.Prime g) (ha : Function.Injective a)
    (hdiv : ∀ i, ((a i).val : ℤ) ∣ n) : M ≤ P.omegaGroup g n := by
  classical
  let S : Finset ℕ := Finset.univ.image fun i : Fin M => (a i).val
  have hS : S ⊆ (P.primes g).filter (fun p => (p : ℤ) ∣ n) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact Finset.mem_filter.mpr ⟨(a i).property, hdiv i⟩
  have hcard : S.card = M := by
    dsimp [S]
    rw [Finset.card_image_of_injective _]
    · simp
    · intro i j hij
      apply ha
      exact Subtype.ext hij
  calc
    M = S.card := hcard.symm
    _ ≤ ((P.primes g).filter (fun p : ℕ => (p : ℤ) ∣ n)).card := Finset.card_le_card hS
    _ = P.omegaGroup g n := rfl

lemma group_target_list_count_le {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hell : 1 ≤ ell) (g : P.Group) (a : P.Labels (J + ell))
    (n₀ n₁ : ℤ) (ha : P.physical (J + ell) n₀ a) :
    Fintype.card {b : Fin (J + ell) → P.Prime g //
      Function.Injective b ∧ (∀ i, ((b i).val : ℤ) ∣ n₁) ∧
        (∀ i, ν.shared g i → a g i = b i)} ≤
      (P.omegaGroup g n₁ - (J + ell) + (ell + m)) ^ (ell + m) := by
  classical
  let Good : Type := {b : Fin (J + ell) → P.Prime g //
    Function.Injective b ∧ (∀ i, ((b i).val : ℤ) ∣ n₁) ∧
      (∀ i, ν.shared g i → a g i = b i)}
  let freeSlots : Finset (Fin (J + ell)) :=
    Finset.univ.filter (fun i => ¬ ν.shared g i)
  let Free := {i : Fin (J + ell) // i ∈ freeSlots}
  let divisors : Finset ℕ := (P.primes g).filter (fun p => (p : ℤ) ∣ n₁)
  let sharedValues : Finset ℕ :=
    (Finset.univ \ ν.changed g).image fun j => (a g (ν.slot j)).val
  let remaining : Finset ℕ := divisors \ sharedValues
  have hchangedJ : (ν.changed g).card ≤ J := by
    simpa using (Finset.card_le_card (Finset.subset_univ (ν.changed g)))
  have hslot : Function.Injective ν.slot := by
    intro i j hij
    apply Fin.ext
    simpa [Pattern.slot] using congrArg Fin.val hij
  have hsource : Function.Injective (fun j : Fin J => (a g (ν.slot j)).val) := by
    intro i j hij
    apply hslot
    apply (ha g).1
    exact Subtype.ext hij
  have hsharedValuesCard : sharedValues.card = J - (ν.changed g).card := by
    dsimp [sharedValues]
    rw [Finset.card_image_of_injective _ hsource,
      Finset.card_sdiff_of_subset (Finset.subset_univ (ν.changed g))]
    simp
  have hfreeCard : Fintype.card Free ≤ ell + m := by
    have hcard : Fintype.card Free = freeSlots.card := by simp [Free]
    rw [hcard]
    exact nonshared_slot_count_le ν g
  by_cases hGood : Nonempty Good
  · let b₀ : Good := Classical.choice hGood
    have hM : J + ell ≤ P.omegaGroup g n₁ :=
      omegaGroup_ge_of_injective_dividing g n₁ b₀.1 b₀.2.1 b₀.2.2.1
    have hsharedSubset : sharedValues ⊆ divisors := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
      have hshared : ν.shared g (ν.slot j) := ⟨j, rfl, (Finset.mem_sdiff.mp hj).2⟩
      have heq := b₀.2.2.2 (ν.slot j) hshared
      exact Finset.mem_filter.mpr ⟨(a g (ν.slot j)).property,
        by rw [heq]; exact b₀.2.2.1 (ν.slot j)⟩
    have hremainingCard : remaining.card ≤ P.omegaGroup g n₁ - (J + ell) + (ell + m) := by
      have hcard : remaining.card = P.omegaGroup g n₁ - (J - (ν.changed g).card) := by
        dsimp [remaining, divisors]
        rw [Finset.card_sdiff_of_subset hsharedSubset, hsharedValuesCard]
        rfl
      rw [hcard]
      have hchangedm : (ν.changed g).card ≤ m := ν.bound g
      omega
    let targetMap : Good → Free → {p : ℕ // p ∈ remaining} := fun b i =>
      ⟨(b.1 i.1).val, by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨(b.1 i.1).property, b.2.2.1 i.1⟩, ?_⟩
        intro hp
        rcases Finset.mem_image.mp hp with ⟨j, hj, hval⟩
        have hshared : ν.shared g (ν.slot j) := ⟨j, rfl, (Finset.mem_sdiff.mp hj).2⟩
        have hmatch := b.2.2.2 (ν.slot j) hshared
        have hEq : b.1 i.1 = b.1 (ν.slot j) := by
          apply Subtype.ext
          calc
            (b.1 i.1).val = (a g (ν.slot j)).val := hval.symm
            _ = (b.1 (ν.slot j)).val := congrArg Subtype.val hmatch
        have hidx : i.1 = ν.slot j := b.2.1 hEq
        exact (Finset.mem_filter.mp i.2).2 (hidx ▸ hshared)⟩
    have htargetMapInj : Function.Injective targetMap := by
      intro b c hbc
      apply Subtype.ext
      funext i
      by_cases hshared : ν.shared g i
      · exact (b.2.2.2 i hshared).symm.trans (c.2.2.2 i hshared)
      · let iFree : Free := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshared⟩⟩
        have hv := congrArg (fun f : Free → {p : ℕ // p ∈ remaining} => f iFree) hbc
        have hvval : (b.1 i).val = (c.1 i).val := by
          simpa [targetMap] using congrArg (fun q : {p : ℕ // p ∈ remaining} => q.val) hv
        exact Subtype.ext hvval
    have hcards : Fintype.card Good ≤ Fintype.card (Free → {p : ℕ // p ∈ remaining}) :=
      Fintype.card_le_of_injective targetMap htargetMapInj
    have hbound : Fintype.card (Free → {p : ℕ // p ∈ remaining}) ≤
        (P.omegaGroup g n₁ - (J + ell) + (ell + m)) ^ (ell + m) := by
      rw [Fintype.card_fun]
      have hrem : Fintype.card {p : ℕ // p ∈ remaining} = remaining.card := by simp
      rw [hrem]
      have hbase : 0 < P.omegaGroup g n₁ - (J + ell) + (ell + m) := by
        have hEll : 1 ≤ ell + m := by omega
        omega
      calc
        remaining.card ^ Fintype.card Free ≤
            (P.omegaGroup g n₁ - (J + ell) + (ell + m)) ^ Fintype.card Free :=
          Nat.pow_le_pow_left hremainingCard _
        _ ≤ (P.omegaGroup g n₁ - (J + ell) + (ell + m)) ^ (ell + m) :=
          Nat.pow_le_pow_right hbase hfreeCard
    exact hcards.trans hbound
  · have hEmpty : IsEmpty Good := ⟨fun b => hGood ⟨b⟩⟩
    have hcard : Fintype.card Good = 0 := Fintype.card_eq_zero_iff.mpr hEmpty
    rw [hcard]
    exact Nat.zero_le _

lemma target_label_count_le {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hell : 1 ≤ ell) (a : P.Labels (J + ell))
    (n₀ n₁ : ℤ) (ha : P.physical (J + ell) n₀ a) :
    Fintype.card {b : P.Labels (J + ell) //
      P.physical (J + ell) n₁ b ∧ ν.compatible a b} ≤
      ∏ g : P.Group, (P.omegaGroup g n₁ - (J + ell) + (ell + m)) ^ (ell + m) := by
  classical
  let Good (g : P.Group) := {b : Fin (J + ell) → P.Prime g //
    Function.Injective b ∧ (∀ i, ((b i).val : ℤ) ∣ n₁) ∧
      (∀ i, ν.shared g i → a g i = b i)}
  let AllGood := {b : P.Labels (J + ell) //
    P.physical (J + ell) n₁ b ∧ ν.compatible a b}
  let e : AllGood ≃ (∀ g : P.Group, Good g) := {
    toFun := fun b g => ⟨b.1 g, ⟨(b.2.1 g).1, (b.2.1 g).2, b.2.2 g⟩⟩
    invFun := fun b => ⟨(fun g => (b g).1), by
      constructor
      · intro g
        exact ⟨(b g).2.1, (b g).2.2.1⟩
      · intro g i hi
        exact (b g).2.2.2 i hi⟩
    left_inv := by
      intro b
      apply Subtype.ext
      funext g
      rfl
    right_inv := by
      intro b
      funext g
      apply Subtype.ext
      rfl
  }
  have hcard : Fintype.card AllGood = ∏ g : P.Group, Fintype.card (Good g) := by
    rw [Fintype.card_congr e, Fintype.card_pi]
  calc
    Fintype.card AllGood = ∏ g : P.Group, Fintype.card (Good g) := hcard
    _ ≤ ∏ g : P.Group,
        (P.omegaGroup g n₁ - (J + ell) + (ell + m)) ^ (ell + m) := by
      apply Finset.prod_le_prod
      intro g hg
      exact group_target_list_count_le ν hell g a n₀ n₁ ha

lemma product_target_weight_bound {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (ν : Pattern P J F.ell m) (n : ℤ)
    (hV : ∀ g : P.Group, F.vMin ≤ P.V g) :
    ∃ C : ℝ, 0 < C ∧
      (∏ g : P.Group,
        (P.V g) ^ (-(ν.t g : ℤ)) *
          (((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m)) *
          F.q ^ (((P.omegaGroup g n - (J + F.ell) : ℕ) : ℝ) / 2)) ≤ C ^ P.count := by
  classical
  obtain ⟨C, hC, hgroupBound⟩ := damped_polynomial_factor_bound F.q F.vMin
    F.q_pos F.q_lt F.vMin_pos (F.ell + m)
  refine ⟨C, hC, ?_⟩
  calc
    (∏ g : P.Group,
        (P.V g) ^ (-(ν.t g : ℤ)) *
          (((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m)) *
          F.q ^ (((P.omegaGroup g n - (J + F.ell) : ℕ) : ℝ) / 2)) ≤
        ∏ _g : P.Group, C := by
      apply Finset.prod_le_prod₀
      · intro g hg
        have hVpos : 0 < P.V g := lt_of_lt_of_le F.vMin_pos (hV g)
        exact mul_nonneg
          (mul_nonneg (zpow_pos hVpos _).le (pow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg F.q_pos.le _)
      intro g hg
      have ht : ν.t g ≤ F.ell + m := by
        dsimp [Pattern.t]
        exact Nat.add_le_add_left (ν.bound g) F.ell
      simpa [Pattern.t] using hgroupBound
        (P.omegaGroup g n - (J + F.ell)) (ν.t g) (P.V g) ht (hV g)
    _ = C ^ P.count := by simp

lemma product_target_weight_bound_of_C {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (ν : Pattern P J F.ell m) (n : ℤ) (hV : ∀ g : P.Group, F.vMin ≤ P.V g)
    (C : ℝ)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    (∏ g : P.Group,
      (P.V g) ^ (-(ν.t g : ℤ)) *
        (((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m)) *
        F.q ^ (((P.omegaGroup g n - (J + F.ell) : ℕ) : ℝ) / 2)) ≤ C ^ P.count := by
  classical
  calc
    (∏ g : P.Group,
        (P.V g) ^ (-(ν.t g : ℤ)) *
          (((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m)) *
          F.q ^ (((P.omegaGroup g n - (J + F.ell) : ℕ) : ℝ) / 2)) ≤
        ∏ _g : P.Group, C := by
      apply Finset.prod_le_prod₀
      · intro g hg
        have hVpos : 0 < P.V g := lt_of_lt_of_le F.vMin_pos (hV g)
        exact mul_nonneg
          (mul_nonneg (zpow_pos hVpos _).le (pow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg F.q_pos.le _)
      intro g hg
      have ht : ν.t g ≤ F.ell + m := by
        dsimp [Pattern.t]
        exact Nat.add_le_add_left (ν.bound g) F.ell
      simpa [Pattern.t] using hgroupBound
        (P.omegaGroup g n - (J + F.ell)) (ν.t g) (P.V g) ht (hV g)
    _ = C ^ P.count := by simp

lemma physical_target_mass_damping_count_le {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (ν : Pattern P J F.ell m) (n : ℤ)
    (b : P.Labels (J + F.ell)) (hb : P.physical (J + F.ell) n b)
    (hV : ∀ g : P.Group, F.vMin ≤ P.V g) (C : ℝ)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    ν.physicalTargetMass * A.damping n *
      (∏ g : P.Group,
        (((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) ^ (F.ell + m) : ℕ) : ℝ)) ≤
      C ^ P.count := by
  classical
  calc
    ν.physicalTargetMass * A.damping n *
        (∏ g : P.Group,
          (((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) ^ (F.ell + m) : ℕ) : ℝ))
      = ∏ g : P.Group,
          ((P.V g) ^ (-(ν.t g : ℤ)) *
            F.q ^ (((P.omegaGroup g n - (J + F.ell) : ℕ) : ℝ) / 2) *
            ((P.omegaGroup g n - (J + F.ell) + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m)) := by
          rw [Pattern.physicalTargetMass, damping_eq_group_product_of_physical A n b hb,
            ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro g hg
          simp [Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ C ^ P.count := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        product_target_weight_bound_of_C ν n hV C hgroupBound

lemma sum_target_coefficient_norm_le {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (v : Fin A.patternCount) (u : P.Aux J)
    (n₀ n₁ : ℤ) (a : P.Labels (J + F.ell))
    (ha : P.physical (J + F.ell) n₀ a) :
    (∑ b : P.Labels (J + F.ell),
      if P.physical (J + F.ell) n₁ b ∧ (A.pattern v).compatible a b then
        ‖(A.pattern v).coefficient (P.restrictBig a) (P.restrictBig b)
          (fun g => u g.val)‖ else 0) ≤
      sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
          ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) * ∏ g : P.Group,
        (P.omegaGroup g n₁ - (J + F.ell) + (F.ell + m)) ^ (F.ell + m) := by
  classical
  let good : P.Labels (J + F.ell) → Prop := fun b =>
    P.physical (J + F.ell) n₁ b ∧ (A.pattern v).compatible a b
  let coeff : P.Labels (J + F.ell) → ℝ := fun b =>
    ‖(A.pattern v).coefficient (P.restrictBig a) (P.restrictBig b) (fun g => u g.val)‖
  let csup : ℝ := sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
    ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖))
  have hsupNonneg : 0 ≤ csup := by
    have hle := coefficient_norm_le_patternSup A v (P.restrictBig a) (P.restrictBig a)
      (fun g => u g.val)
    exact (norm_nonneg _).trans (by simpa [csup] using hle)
  have hsum : (∑ b : P.Labels (J + F.ell), if good b then coeff b else 0) ≤
      ∑ b : P.Labels (J + F.ell), if good b then csup else 0 := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases hgood : good b
    · simp [hgood, coeff]
      exact coefficient_norm_le_patternSup A v (P.restrictBig a) (P.restrictBig b)
        (fun g => u g.val)
    · simp [hgood]
  have hconst : (∑ b : P.Labels (J + F.ell), if good b then csup else 0) =
      csup * Fintype.card {b : P.Labels (J + F.ell) // good b} := by
    rw [← Finset.sum_filter]
    simp [Fintype.card_subtype, mul_comm]
  have hcount := target_label_count_le (A.pattern v) F.ell_pos a n₀ n₁ ha
  calc
    (∑ b : P.Labels (J + F.ell), if good b then coeff b else 0) ≤
        csup * Fintype.card {b : P.Labels (J + F.ell) // good b} := by
          rw [← hconst]
          exact hsum
    _ ≤ csup *
        ∏ g : P.Group, (P.omegaGroup g n₁ - (J + F.ell) + (F.ell + m)) ^ (F.ell + m) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hsupNonneg

lemma physicalRaw_norm_le_terms {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (x : ℝ) (hP : P.Admissible F x)
    (z z' : A.State) (hz : P.physical (J + F.ell) z.1 z.2) :
    ‖A.physicalRaw true z z'‖ ≤
      ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
        if P.physical (J + F.ell) z'.1 z'.2 ∧
            (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
            z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
          ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
            A.damping z.1 * A.damping z'.1) *
            ‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
              (fun g => u g.val)‖
        else 0 := by
  classical
  by_cases hz' : P.physical (J + F.ell) z'.1 z'.2
  · have hV : ∀ g : P.Group, 0 < P.V g := fun g => V_pos_of_admissible hP g
    rw [Model.physicalRaw, if_pos ⟨hz, hz'⟩]
    calc
      ‖∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          if (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
              z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
            ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
              A.damping z.1 * A.damping z'.1 : ℝ) *
              ((‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                  (fun g => u g.val) *
                imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖ : ℝ) : ℂ)
          else 0‖ ≤
        ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          ‖if (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
              z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
            ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
              A.damping z.1 * A.damping z'.1 : ℝ) *
              ((‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                  (fun g => u g.val) *
                imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖ : ℝ) : ℂ)
          else 0‖ := by
            calc
              _ ≤ ∑ v : Fin A.patternCount, ‖∑ u : P.Aux J,
                  if (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
                      z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
                    ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
                      A.damping z.1 * A.damping z'.1 : ℝ) *
                      ((‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                          (fun g => u g.val) *
                        imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖ : ℝ) : ℂ)
                  else 0‖ := norm_sum_le _ _
              _ ≤ ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
                  ‖if (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
                      z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
                    ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
                      A.damping z.1 * A.damping z'.1 : ℝ) *
                      ((‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                          (fun g => u g.val) *
                        imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖ : ℝ) : ℂ)
                  else 0‖ := by
                apply Finset.sum_le_sum
                intro v hv
                exact norm_sum_le _ _
      _ = ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          if P.physical (J + F.ell) z'.1 z'.2 ∧
              (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
              z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
            ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
              A.damping z.1 * A.damping z'.1) *
              ‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                (fun g => u g.val)‖
          else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hcond : (A.pattern v).compatible z.2 z'.2 ∧
            (A.pattern v).ban z.2 z'.2 u ∧ z'.1 = z.1 +
              A.k * ((A.pattern v).D z.2 u : ℤ)
        · have htargetAtPos : P.physical (J + F.ell)
              (z.1 + A.k * ((A.pattern v).D z.2 u : ℤ)) z'.2 := by
            rw [← hcond.2.2]
            exact hz'
          have hweightAtPos : 0 < (A.pattern v).auxMass u *
              (A.pattern v).physicalTargetMass * A.damping z.1 *
              A.damping (z.1 + A.k * ((A.pattern v).D z.2 u : ℤ)) :=
            mul_pos (mul_pos (mul_pos (auxMass_pos_of_admissible (A.pattern v) u hP)
              (physicalTargetMass_pos_of_admissible (A.pattern v) hV))
              (damping_pos A z.1))
              (damping_pos A (z.1 + A.k * ((A.pattern v).D z.2 u : ℤ)))
          have hnorm :
              ‖((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
                  A.damping z.1 * A.damping (z.1 + A.k *
                    ((A.pattern v).D z.2 u : ℤ)) : ℝ) *
                (‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                  (fun g => u g.val) * imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖ : ℂ)‖ =
              (A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
                A.damping z.1 * A.damping (z.1 + A.k *
                  ((A.pattern v).D z.2 u : ℤ)) *
                ‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
                  (fun g => u g.val)‖ := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos hweightAtPos, abs_of_nonneg (norm_nonneg _)]
            rw [norm_mul, norm_imaginaryPower, mul_one]
          simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            auxMass_pos_of_admissible (A.pattern v) u hP,
            physicalTargetMass_pos_of_admissible (A.pattern v) hV,
            damping_pos A z.1,
            damping_pos A (z.1 + A.k * ((A.pattern v).D z.2 u : ℤ)),
            norm_imaginaryPower, abs_of_nonneg (norm_nonneg _), hcond, htargetAtPos] using hnorm
        · simp [hz', hcond]
  · have hnot : ¬ (P.physical (J + F.ell) z.1 z.2 ∧
        P.physical (J + F.ell) z'.1 z'.2) := fun h => hz' h.2
    rw [Model.physicalRaw, if_neg hnot]
    simp [hz']

lemma raw_transition_target_sum_le {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (x : ℝ) (hP : P.Admissible F x)
    (n : ℤ) (a : P.Labels (J + F.ell)) (ha : P.physical (J + F.ell) n a)
    (v : Fin A.patternCount) (u : P.Aux J) (C : ℝ) (hC : 0 < C)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    (∑ z' ∈ possiblePhysicalTargets A n,
      if P.physical (J + F.ell) z'.1 z'.2 ∧
          (A.pattern v).compatible a z'.2 ∧ (A.pattern v).ban a z'.2 u ∧
          z'.1 = n + A.k * ((A.pattern v).D a u : ℤ) then
        ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
          A.damping n * A.damping z'.1) *
          ‖(A.pattern v).coefficient (P.restrictBig a) (P.restrictBig z'.2)
            (fun g => u g.val)‖
      else 0) ≤
      (A.pattern v).auxMass u * A.damping n *
        sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
          ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) * C ^ P.count := by
  classical
  let ν := A.pattern v
  let n' := n + A.k * (ν.D a u : ℤ)
  let good : P.Labels (J + F.ell) → Prop := fun b =>
    P.physical (J + F.ell) n' b ∧ ν.compatible a b
  let coeff : P.Labels (J + F.ell) → ℝ := fun b =>
    ‖ν.coefficient (P.restrictBig a) (P.restrictBig b) (fun g => u g.val)‖
  let csup : ℝ := sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
    ‖ν.coefficient z.1 z.2.1 z.2.2‖))
  let f : A.State → ℝ := fun z' =>
    if P.physical (J + F.ell) z'.1 z'.2 ∧ ν.compatible a z'.2 ∧
        ν.ban a z'.2 u ∧ z'.1 = n' then
      (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping z'.1) *
        ‖ν.coefficient (P.restrictBig a) (P.restrictBig z'.2) (fun g => u g.val)‖
    else 0
  have hlabels : ∀ b : P.Labels (J + F.ell), (n', b) ∈ possiblePhysicalTargets A n := by
    intro b
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨(v, (a, u)), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_univ _
  have hzero : ∀ z' ∈ possiblePhysicalTargets A n, z'.1 ≠ n' → f z' = 0 := by
    intro z' hz' hpos
    simp [f, hpos]
  have hpositionSum :
      (∑ z' ∈ possiblePhysicalTargets A n, f z') =
        ∑ b : P.Labels (J + F.ell),
          if good b ∧ ν.ban a b u then
            (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') * coeff b
          else 0 := by
    simpa [f, good, coeff, n', and_assoc] using
      finset_sum_supported_at_position (possiblePhysicalTargets A n) n' f hlabels hzero
  have hweight : 0 < ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n' :=
    mul_pos (mul_pos (mul_pos (auxMass_pos_of_admissible ν u hP)
      (physicalTargetMass_pos_of_admissible ν (fun g => V_pos_of_admissible hP g)))
      (damping_pos A n)) (damping_pos A n')
  have hgoodSum : (∑ b : P.Labels (J + F.ell), if good b then coeff b else 0) ≤
      csup *
        ∏ g : P.Group, (P.omegaGroup g n' - (J + F.ell) + (F.ell + m)) ^ (F.ell + m) := by
    simpa [ν] using sum_target_coefficient_norm_le A v u n n' a ha
  have hbanDrop :
      (∑ b : P.Labels (J + F.ell),
        if good b ∧ ν.ban a b u then
          (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') * coeff b
        else 0) ≤
        (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') *
          ∑ b : P.Labels (J + F.ell), if good b then coeff b else 0 := by
    calc
      (∑ b : P.Labels (J + F.ell),
        if good b ∧ ν.ban a b u then
          (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') * coeff b
        else 0) ≤
        ∑ b : P.Labels (J + F.ell),
          if good b then
            (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') * coeff b
          else 0 := by
          apply Finset.sum_le_sum
          intro b hb
          by_cases hg : good b
          · by_cases hban : ν.ban a b u <;> simp [hg, hban] <;> positivity
          · simp [hg]
      _ = (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') *
            ∑ b : P.Labels (J + F.ell), if good b then coeff b else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hg : good b <;> simp [hg]
  have hcoefNonneg : 0 ≤ csup := by
    have hle := coefficient_norm_le_patternSup A v (P.restrictBig a) (P.restrictBig a)
      (fun g => u g.val)
    exact (norm_nonneg _).trans (by simpa [ν, csup] using hle)
  have hgoodSum' : (∑ b : P.Labels (J + F.ell), if good b then coeff b else 0) ≤
      csup * (∏ g : P.Group,
        (((P.omegaGroup g n' - (J + F.ell) + (F.ell + m) : ℕ) ^ (F.ell + m) : ℕ) : ℝ)) := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using hgoodSum
  have hsourceWeightNonneg : 0 ≤ ν.auxMass u * A.damping n :=
    mul_nonneg (auxMass_pos_of_admissible ν u hP).le (damping_pos A n).le
  have htailNonneg : 0 ≤ ν.physicalTargetMass * A.damping n' :=
    mul_nonneg (physicalTargetMass_pos_of_admissible ν
      (fun g => V_pos_of_admissible hP g)).le (damping_pos A n').le
  change (∑ z' ∈ possiblePhysicalTargets A n, f z') ≤
    (ν.auxMass u * A.damping n) * csup * C ^ P.count
  by_cases hGood : Nonempty {b : P.Labels (J + F.ell) // good b}
  · let b₀ : {b : P.Labels (J + F.ell) // good b} := Classical.choice hGood
    have hweightCount := physical_target_mass_damping_count_le A ν n' b₀.1 b₀.2.1
      (V_lower_of_admissible hP) C hgroupBound
    calc
      (∑ z' ∈ possiblePhysicalTargets A n, f z') ≤
          (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') *
            ∑ b : P.Labels (J + F.ell), if good b then coeff b else 0 := by
        rw [hpositionSum]
        exact hbanDrop
      _ = (ν.auxMass u * A.damping n) *
          (ν.physicalTargetMass * A.damping n' *
            ∑ b : P.Labels (J + F.ell), if good b then coeff b else 0) := by ring
      _ ≤ (ν.auxMass u * A.damping n) *
          (ν.physicalTargetMass * A.damping n' *
            (csup * ∏ g : P.Group,
              (((P.omegaGroup g n' - (J + F.ell) + (F.ell + m) : ℕ) ^ (F.ell + m) : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hgoodSum' htailNonneg
        · exact hsourceWeightNonneg
      _ = (ν.auxMass u * A.damping n) *
          csup * (ν.physicalTargetMass * A.damping n' *
              ∏ g : P.Group,
                (((P.omegaGroup g n' - (J + F.ell) + (F.ell + m) : ℕ) ^ (F.ell + m) : ℕ) : ℝ)) := by ring
      _ ≤ (ν.auxMass u * A.damping n * csup) * C ^ P.count :=
        mul_le_mul_of_nonneg_left hweightCount (mul_nonneg hsourceWeightNonneg hcoefNonneg)
      _ = (ν.auxMass u * A.damping n) *
          csup * C ^ P.count := by ring
  · have hcoeffZero : (∑ b : P.Labels (J + F.ell), if good b then coeff b else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hg : good b
      · exact (hGood ⟨b, hg⟩).elim
      · simp [hg]
    have hsumZero : (∑ z' ∈ possiblePhysicalTargets A n, f z') ≤ 0 := by
      calc
        _ = ∑ b : P.Labels (J + F.ell),
            if good b ∧ ν.ban a b u then
              (ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n') * coeff b
            else 0 := hpositionSum
        _ ≤ 0 := by simpa [hcoeffZero] using hbanDrop
    have hright : 0 ≤ (ν.auxMass u * A.damping n) *
        csup * C ^ P.count := by
      exact mul_nonneg (mul_nonneg hsourceWeightNonneg hcoefNonneg)
        (pow_nonneg hC.le _)
    exact hsumZero.trans hright

lemma physicalRaw_row_sum_bound {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (x : ℝ) (hP : P.Admissible F x)
    (n : ℤ) (a : P.Labels (J + F.ell))
    (ha : P.physical (J + F.ell) n a) (C : ℝ) (hC : 0 < C)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    (∑ z' ∈ possiblePhysicalTargets A n, ‖A.physicalRaw true (n, a) z'‖) ≤
      A.patternMass * C ^ P.count := by
  classical
  have hV : ∀ g : P.Group, 0 < P.V g := fun g => V_pos_of_admissible hP g
  have hVne : ∀ g : P.Group, P.V g ≠ 0 := fun g => (hV g).ne'
  have hAux (v : Fin A.patternCount) :
      (∑ u : P.Aux J, (A.pattern v).auxMass u) = 1 := by
    simpa [Pattern.auxMass] using sum_auxiliary_mass_eq_one P J hVne
  let supv : Fin A.patternCount → ℝ := fun v =>
    sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
      ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖))
  have hsourceDamp : A.damping n ≤ 1 := damping_le_one_of_physical A n a ha
  have hsourceDampNonneg : 0 ≤ A.damping n := (damping_pos A n).le
  have hpatternSups : (∑ v : Fin A.patternCount, supv v) = A.patternMass := rfl
  have hpatternNonneg : 0 ≤ A.patternMass := patternMass_nonneg A
  have hCpow : 0 ≤ C ^ P.count := pow_nonneg hC.le _
  have hrawBound :
      (∑ z' ∈ possiblePhysicalTargets A n, ‖A.physicalRaw true (n, a) z'‖) ≤
        ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          (A.pattern v).auxMass u * A.damping n * supv v * C ^ P.count := by
    calc
      (∑ z' ∈ possiblePhysicalTargets A n, ‖A.physicalRaw true (n, a) z'‖) ≤
          ∑ z' ∈ possiblePhysicalTargets A n, ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
            if P.physical (J + F.ell) z'.1 z'.2 ∧
                (A.pattern v).compatible a z'.2 ∧ (A.pattern v).ban a z'.2 u ∧
                z'.1 = n + A.k * ((A.pattern v).D a u : ℤ) then
              ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
                A.damping n * A.damping z'.1) *
                ‖(A.pattern v).coefficient (P.restrictBig a) (P.restrictBig z'.2)
                  (fun g => u g.val)‖
            else 0 := by
        apply Finset.sum_le_sum
        intro z' hz'
        exact physicalRaw_norm_le_terms A x hP (n, a) z' ha
      _ = ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          ∑ z' ∈ possiblePhysicalTargets A n,
            if P.physical (J + F.ell) z'.1 z'.2 ∧
                (A.pattern v).compatible a z'.2 ∧ (A.pattern v).ban a z'.2 u ∧
                z'.1 = n + A.k * ((A.pattern v).D a u : ℤ) then
              ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
                A.damping n * A.damping z'.1) *
                ‖(A.pattern v).coefficient (P.restrictBig a) (P.restrictBig z'.2)
                  (fun g => u g.val)‖
            else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.sum_comm]
      _ ≤ ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          (A.pattern v).auxMass u * A.damping n *
            sSup (Set.range (fun z : A.BigLabels × A.BigLabels × P.BigAux J =>
              ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) * C ^ P.count := by
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.sum_le_sum
        intro u hu
        simpa [supv] using raw_transition_target_sum_le A x hP n a ha v u C hC hgroupBound
  calc
    (∑ z' ∈ possiblePhysicalTargets A n, ‖A.physicalRaw true (n, a) z'‖) ≤
        ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
          (A.pattern v).auxMass u * A.damping n * supv v * C ^ P.count := hrawBound
    _ = A.damping n * C ^ P.count * A.patternMass := by
      calc
        _ = ∑ v : Fin A.patternCount, (A.damping n * C ^ P.count * supv v) := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            (∑ u : P.Aux J,
                (A.pattern v).auxMass u * A.damping n * supv v * C ^ P.count) =
                (A.damping n * C ^ P.count * supv v) *
                  ∑ u : P.Aux J, (A.pattern v).auxMass u := by
              calc
                _ = ∑ u : P.Aux J, (A.damping n * C ^ P.count * supv v) *
                    (A.pattern v).auxMass u := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  ring
                _ = _ := by rw [Finset.mul_sum]
            _ = A.damping n * C ^ P.count * supv v := by
              rw [hAux v]
              ring
        _ = A.damping n * C ^ P.count * (∑ v : Fin A.patternCount, supv v) := by
          rw [← Finset.mul_sum]
        _ = A.damping n * C ^ P.count * A.patternMass := by rw [hpatternSups]
    _ ≤ A.patternMass * C ^ P.count := by
      calc
        A.damping n * C ^ P.count * A.patternMass ≤ 1 * C ^ P.count * A.patternMass := by
          gcongr
        _ = A.patternMass * C ^ P.count := by ring

lemma physicalRaw_row_sum_perm_bound {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (x : ℝ) (hP : P.Admissible F x)
    (n : ℤ) (a : P.Labels (J + F.ell)) (ha : P.physical (J + F.ell) n a)
    (π : P.Permutations (J + F.ell)) (τ : P.Permutations (J + F.ell))
    (C : ℝ) (hC : 0 < C)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    (∑ z' ∈ possiblePhysicalTargets A n,
      ‖A.physicalRaw true (n, P.act π a) (z'.1, P.act τ z'.2)‖) ≤
      A.patternMass * C ^ P.count := by
  rw [sum_possibleTargets_act A n τ (fun z' => ‖A.physicalRaw true (n, P.act π a) z'‖)]
  exact physicalRaw_row_sum_bound A x hP n (P.act π a)
    (physical_act π n a ha) C hC hgroupBound

def swapPatternCoefficient {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) : Pattern P J ell m where
  changed := ν.changed
  small := ν.small
  bound := ν.bound
  coefficient := fun a b u => ν.coefficient b a u
  coefficient_aux_ext := by
    intro a b u v huv
    exact ν.coefficient_aux_ext b a u v huv

def reversePhysicalModel {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) : Model F P J m where
  patternCount := A.patternCount
  pattern := fun v => swapPatternCoefficient (A.pattern v)
  k := -A.k
  zeta := A.zeta

lemma pattern_D_eq_of_compatible {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u : P.Aux J)
    (hab : ν.compatible a b) : ν.D a u = ν.D b u := by
  classical
  simp only [Pattern.D]
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hchanged : i ∈ ν.changed g
  · simp [hchanged]
  · have hshared : ν.shared g (ν.slot i) := ⟨i, rfl, hchanged⟩
    simp [hchanged, hab g (ν.slot i) hshared]

lemma reversePhysicalModel_patternMass {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) : (reversePhysicalModel A).patternMass = A.patternMass := by
  classical
  unfold Model.patternMass reversePhysicalModel
  apply Finset.sum_congr rfl
  intro v hv
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(z.2.1, z.1, z.2.2), ?_⟩
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨(z.2.1, z.1, z.2.2), ?_⟩
    rfl

lemma physicalRaw_reverse_eq {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n n' : ℤ) (a b : A.Labels) :
    A.physicalRaw true (n', b) (n, a) =
      (reversePhysicalModel A).physicalRaw true (n, a) (n', b) := by
  classical
  unfold reversePhysicalModel
  by_cases hsrc : P.physical (J + F.ell) n' b
  · by_cases htgt : P.physical (J + F.ell) n a
    · unfold Model.physicalRaw
      rw [if_pos ⟨hsrc, htgt⟩, if_pos ⟨htgt, hsrc⟩]
      simp only [if_true]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      let ν := A.pattern v
      let νrev := swapPatternCoefficient ν
      have hcompatible : ν.compatible b a ↔ νrev.compatible a b := by
        constructor
        · intro h g i hi
          exact (h g i hi).symm
        · intro h g i hi
          exact (h g i hi).symm
      have hban : ν.ban b a u ↔ νrev.ban a b u := by
        simp [νrev, swapPatternCoefficient, Pattern.ban, and_comm]
      have hDrev : νrev.D a u = ν.D a u := rfl
      have hpos (hD : ν.D b u = ν.D a u) :
          (n = n' + A.k * (ν.D b u : ℤ)) ↔
            (n' = n + (-A.k) * (νrev.D a u : ℤ)) := by
        rw [hDrev]
        constructor
        · intro h
          rw [← hD]
          nlinarith [h]
        · intro h
          rw [hD]
          nlinarith [h]
      have hcond (hD : ν.D b u = ν.D a u) :
          (ν.compatible b a ∧ ν.ban b a u ∧ n = n' + A.k * (ν.D b u : ℤ)) ↔
            (νrev.compatible a b ∧ νrev.ban a b u ∧
              n' = n + (-A.k) * (νrev.D a u : ℤ)) := by
        constructor
        · rintro ⟨hc, hb, hp⟩
          exact ⟨hcompatible.mp hc, hban.mp hb, (hpos hD).mp hp⟩
        · rintro ⟨hc, hb, hp⟩
          exact ⟨hcompatible.mpr hc, hban.mpr hb, (hpos hD).mpr hp⟩
      by_cases hL : ν.compatible b a ∧ ν.ban b a u ∧
          n = n' + A.k * (ν.D b u : ℤ)
      · have hD := pattern_D_eq_of_compatible ν b a u hL.1
        have hR := (hcond hD).mp hL
        have hterm :
            ((ν.auxMass u * ν.physicalTargetMass * A.damping n' * A.damping n : ℝ) *
              (‖ν.coefficient (P.restrictBig b) (P.restrictBig a) (fun g => u g.val) *
                imaginaryPower (ν.D b u) A.zeta‖ : ℂ)) =
            ((νrev.auxMass u * νrev.physicalTargetMass *
                (reversePhysicalModel A).damping n * (reversePhysicalModel A).damping n' : ℝ) *
              (‖νrev.coefficient (P.restrictBig a) (P.restrictBig b) (fun g => u g.val) *
                imaginaryPower (νrev.D a u) A.zeta‖ : ℂ)) := by
          change
            ((ν.auxMass u * ν.physicalTargetMass * A.damping n' * A.damping n : ℝ) *
              (‖ν.coefficient (P.restrictBig b) (P.restrictBig a) (fun g => u g.val) *
                imaginaryPower (ν.D b u) A.zeta‖ : ℂ)) =
            ((ν.auxMass u * ν.physicalTargetMass * A.damping n * A.damping n' : ℝ) *
              (‖ν.coefficient (P.restrictBig b) (P.restrictBig a) (fun g => u g.val) *
                imaginaryPower (ν.D a u) A.zeta‖ : ℂ))
          rw [hD]
          ring_nf
        rw [if_pos hL, if_pos hR]
        exact hterm
      · have hR : ¬(νrev.compatible a b ∧ νrev.ban a b u ∧
            n' = n + (-A.k) * (νrev.D a u : ℤ)) := by
          intro hr
          have hc : ν.compatible b a := hcompatible.mpr hr.1
          have hD := pattern_D_eq_of_compatible ν b a u hc
          exact hL ((hcond hD).mpr hr)
        rw [if_neg hL, if_neg hR]
    · simp [Model.physicalRaw, swapPatternCoefficient, htgt]
  · simp [Model.physicalRaw, swapPatternCoefficient, hsrc]

lemma physicalKernel_reverse_eq {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n n' : ℤ) (a b : A.Labels) :
    A.physicalKernel true (n', b) (n, a) =
      (reversePhysicalModel A).physicalKernel true (n, a) (n', b) := by
  classical
  unfold Model.physicalKernel
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro τ hτ
  exact physicalRaw_reverse_eq A n n' (P.act π a) (P.act τ b)

lemma physicalKernel_row_bound_of_C {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (x : ℝ) (hP : P.Admissible F x)
    (n : ℤ) (a : P.Labels (J + F.ell)) (ha : P.physical (J + F.ell) n a)
    (C : ℝ) (hC : 0 < C)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    (∑' z' : A.State, (A.physicalKernel true (n, a) z').re) ≤
      A.patternMass * C ^ P.count := by
  classical
  let Perm := P.Permutations (J + F.ell)
  let Idx := Perm × Perm
  let c : ℂ := ((Fintype.card Perm : ℂ) ^ 2)⁻¹
  let K : Idx → A.State → ℂ := fun q z' =>
    A.physicalRaw true (n, P.act q.1 a) (z'.1, P.act q.2 z'.2)
  have hkEq (z' : A.State) :
      A.physicalKernel true (n, a) z' = c * ∑ q : Idx, K q z' := by
    simp only [Model.physicalKernel]
    dsimp [c, K, Idx, Perm]
    rw [← Fintype.sum_prod_type
      (fun q : P.Permutations (J + F.ell) × P.Permutations (J + F.ell) =>
        A.physicalRaw true (n, P.act q.1 a) (z'.1, P.act q.2 z'.2))]
  have hKzero : ∀ q z', z' ∉ possiblePhysicalTargets A n → K q z' = 0 := by
    intro q z' hz'
    rcases q with ⟨π, τ⟩
    have hpos : z'.1 ∉ possiblePhysicalPositions A n := by
      intro hmem
      exact hz' (Finset.mem_product.mpr ⟨hmem, Finset.mem_univ _⟩)
    have hact : (z'.1, P.act τ z'.2) ∉ possiblePhysicalTargets A n := by
      intro hmem
      exact hpos (Finset.mem_product.mp hmem).1
    exact physicalRaw_zero_outside_targets A n (P.act π a)
      (z'.1, P.act τ z'.2) hact
  have hnormTsum : (∑' z' : A.State, ‖A.physicalKernel true (n, a) z'‖) ≤
      ‖c‖ * ∑ q : Idx, ∑ z' ∈ possiblePhysicalTargets A n, ‖K q z'‖ := by
    calc
      (∑' z' : A.State, ‖A.physicalKernel true (n, a) z'‖) =
          ∑' z' : A.State, ‖c * ∑ q : Idx, K q z'‖ := by
        apply tsum_congr
        intro z'
        rw [hkEq z']
      _ ≤ ‖c‖ * ∑ q : Idx, ∑ z' ∈ possiblePhysicalTargets A n, ‖K q z'‖ :=
        tsum_norm_finite_average (possiblePhysicalTargets A n) c K hKzero
  have hrows : (∑ q : Idx, ∑ z' ∈ possiblePhysicalTargets A n, ‖K q z'‖) ≤
      (Fintype.card Idx : ℝ) * (A.patternMass * C ^ P.count) := by
    calc
      (∑ q : Idx, ∑ z' ∈ possiblePhysicalTargets A n, ‖K q z'‖) ≤
          ∑ _q : Idx, (A.patternMass * C ^ P.count) := by
        apply Finset.sum_le_sum
        intro q hq
        rcases q with ⟨π, τ⟩
        exact physicalRaw_row_sum_perm_bound A x hP n a ha π τ C hC hgroupBound
      _ = (Fintype.card Idx : ℝ) * (A.patternMass * C ^ P.count) := by simp
  have hpermNonempty : Nonempty Perm := ⟨fun _ => Equiv.refl _⟩
  have hpermPos : 0 < (Fintype.card Perm : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hpermNonempty)
  have hcancel : ‖c‖ * (Fintype.card Idx : ℝ) = 1 := by
    dsimp [c, Idx, Perm]
    rw [norm_inv, norm_pow, Complex.norm_natCast, Fintype.card_prod, Nat.cast_mul]
    field_simp
  have hnormBound : (∑' z' : A.State, ‖A.physicalKernel true (n, a) z'‖) ≤
      A.patternMass * C ^ P.count := by
    calc
      (∑' z' : A.State, ‖A.physicalKernel true (n, a) z'‖) ≤
          ‖c‖ * ∑ q : Idx, ∑ z' ∈ possiblePhysicalTargets A n, ‖K q z'‖ := hnormTsum
      _ ≤ ‖c‖ * ((Fintype.card Idx : ℝ) * (A.patternMass * C ^ P.count)) :=
        mul_le_mul_of_nonneg_left hrows (norm_nonneg _)
      _ = A.patternMass * C ^ P.count := by
        calc
          _ = (‖c‖ * (Fintype.card Idx : ℝ)) * (A.patternMass * C ^ P.count) := by ring
          _ = _ := by rw [hcancel]; ring
  have hsumRe : (∑' z' : A.State, (A.physicalKernel true (n, a) z').re) =
      ∑ z' ∈ possiblePhysicalTargets A n, (A.physicalKernel true (n, a) z').re :=
    tsum_eq_sum (fun z' hz' => by simp [physicalKernel_zero_outside_targets A n a z' hz'])
  have hsumNorm : (∑' z' : A.State, ‖A.physicalKernel true (n, a) z'‖) =
      ∑ z' ∈ possiblePhysicalTargets A n, ‖A.physicalKernel true (n, a) z'‖ :=
    tsum_eq_sum (fun z' hz' => by simp [physicalKernel_zero_outside_targets A n a z' hz'])
  calc
    (∑' z' : A.State, (A.physicalKernel true (n, a) z').re) =
        ∑ z' ∈ possiblePhysicalTargets A n, (A.physicalKernel true (n, a) z').re := hsumRe
    _ ≤ ∑ z' ∈ possiblePhysicalTargets A n, ‖A.physicalKernel true (n, a) z'‖ := by
      apply Finset.sum_le_sum
      intro z' hz'
      exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ = ∑' z' : A.State, ‖A.physicalKernel true (n, a) z'‖ := hsumNorm.symm
    _ ≤ A.patternMass * C ^ P.count := hnormBound

lemma physicalKernel_column_bound_of_C {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (x : ℝ) (hP : P.Admissible F x)
    (n : ℤ) (a : P.Labels (J + F.ell)) (ha : P.physical (J + F.ell) n a)
    (C : ℝ) (hC : 0 < C)
    (hgroupBound : ∀ (z t : ℕ) (V : ℝ), t ≤ F.ell + m → F.vMin ≤ V →
      V ^ (-(t : ℤ)) * ((z + (F.ell + m) : ℕ) : ℝ) ^ (F.ell + m) *
        F.q ^ ((z : ℝ) / 2) ≤ C) :
    (∑' z' : A.State, (A.physicalKernel true z' (n, a)).re) ≤
      A.patternMass * C ^ P.count := by
  calc
    (∑' z' : A.State, (A.physicalKernel true z' (n, a)).re) =
        ∑' z' : A.State,
          ((reversePhysicalModel A).physicalKernel true (n, a) z').re := by
      apply tsum_congr
      intro z'
      rcases z' with ⟨n', b⟩
      exact congrArg Complex.re (physicalKernel_reverse_eq A n n' a b)
    _ ≤ (reversePhysicalModel A).patternMass * C ^ P.count :=
      physicalKernel_row_bound_of_C (reversePhysicalModel A) x hP n a ha C hC hgroupBound
    _ = A.patternMass * C ^ P.count := by rw [reversePhysicalModel_patternMass]

lemma primeGroupCount_le_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) : (P.count : ℝ) ≤ 2 * F.C₀ * T x := by
  classical
  rcases hP with ⟨_, hsmall, _, hbig, _, _⟩
  have hpartition : P.smallGroups.card + P.bigGroups.card = P.count := by
    simpa [PrimeGroups.smallGroups, PrimeGroups.bigGroups] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun g : P.Group => P.big g = false))
  have hcount : (P.count : ℝ) =
      (P.smallGroups.card : ℝ) + (P.bigGroups.card : ℝ) := by
    exact_mod_cast hpartition.symm
  rw [hcount]
  linarith

lemma constant_group_power_le_log_power {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (hL : 1 ≤ L x) (C : ℝ) (hC : 0 < C) :
    C ^ P.count ≤ (L x) ^ (2 * F.C₀ * Real.log (max 1 C)) := by
  let Cbar : ℝ := max 1 C
  have hCbarOne : 1 ≤ Cbar := le_max_left _ _
  have hCbarPos : 0 < Cbar := lt_of_lt_of_le zero_lt_one hCbarOne
  have hlogNonneg : 0 ≤ Real.log Cbar := Real.log_nonneg hCbarOne
  have hcount := primeGroupCount_le_of_admissible hP
  have hCpow : C ^ P.count ≤ Cbar ^ P.count :=
    pow_le_pow_left₀ hC.le (le_max_right _ _) _
  have hpowExp : Cbar ^ P.count = Real.exp (Real.log Cbar * (P.count : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCbarPos]
  have hexpBound : Real.log Cbar * (P.count : ℝ) ≤
      (2 * F.C₀ * Real.log Cbar) * T x := by
    calc
      Real.log Cbar * (P.count : ℝ) ≤
          Real.log Cbar * (2 * F.C₀ * T x) :=
        mul_le_mul_of_nonneg_left hcount hlogNonneg
      _ = (2 * F.C₀ * Real.log Cbar) * T x := by ring
  calc
    C ^ P.count ≤ Cbar ^ P.count := hCpow
    _ = Real.exp (Real.log Cbar * (P.count : ℝ)) := hpowExp
    _ ≤ Real.exp ((2 * F.C₀ * Real.log Cbar) * T x) := Real.exp_le_exp.mpr hexpBound
    _ = (L x) ^ (2 * F.C₀ * Real.log Cbar) := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hL)]
      congr 1
      simp [T]
      ring

theorem physical_schur_proof (F : FixedData) (m : ℕ) (C₁ : ℝ) :
    ∃ Cabs : ℝ, ∀ J : ℕ, ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (P : PrimeGroups),
      P.Admissible F x → ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      (∀ z : A.State, ∑' z', (A.physicalKernel true z z').re ≤ (L x) ^ Cabs) ∧
      (∀ z : A.State, ∑' z', (A.physicalKernel true z' z).re ≤ (L x) ^ Cabs) := by
  classical
  obtain ⟨C, hC, hgroupBound⟩ := damped_polynomial_factor_bound F.q F.vMin
    F.q_pos F.q_lt F.vMin_pos (F.ell + m)
  let Cbar : ℝ := max 1 C
  let E : ℝ := 2 * F.C₀ * Real.log Cbar
  let C₁bar : ℝ := max C₁ 0
  let Cabs : ℝ := C₁bar + E + 1
  let x₀ : ℝ := Real.exp (Real.exp 1)
  refine ⟨Cabs, ?_⟩
  intro J
  refine ⟨x₀, ?_⟩
  intro x hx P hP A hmass
  have hlog : Real.exp 1 ≤ L x := by
    dsimp [x₀] at hx
    have hlog' := Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
    simpa [L] using hlog'
  have hL : 1 ≤ L x := by
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    exact h1.trans hlog
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  have hCbar1 : 1 ≤ Cbar := le_max_left _ _
  have hCbarC : C ≤ Cbar := le_max_right _ _
  have hCbarPos : 0 < Cbar := lt_of_lt_of_le zero_lt_one hCbar1
  have hlogCbar : 0 ≤ Real.log Cbar := Real.log_nonneg hCbar1
  have hgroupPow : C ^ P.count ≤ (L x) ^ E := by
    dsimp [Cbar, E]
    exact constant_group_power_le_log_power hP hL C hC
  have hC₁pow : (L x) ^ C₁ ≤ (L x) ^ C₁bar :=
    Real.rpow_le_rpow_of_exponent_le hL (le_max_left C₁ 0)
  have hmassPow : A.patternMass ≤ (L x) ^ C₁bar := hmass.trans hC₁pow
  have hbound : A.patternMass * C ^ P.count ≤ (L x) ^ Cabs := by
    have hmassNonneg : 0 ≤ A.patternMass := patternMass_nonneg A
    have hLpowNonneg (t : ℝ) : 0 ≤ (L x) ^ t := Real.rpow_nonneg hLpos.le t
    have hExp : C₁bar + E ≤ Cabs := by
      dsimp [Cabs]
      linarith
    calc
      A.patternMass * C ^ P.count ≤ (L x) ^ C₁bar * (L x) ^ E :=
        mul_le_mul hmassPow hgroupPow (pow_nonneg hC.le _) (hLpowNonneg C₁bar)
      _ = (L x) ^ (C₁bar + E) := (Real.rpow_add hLpos C₁bar E).symm
      _ ≤ (L x) ^ Cabs := Real.rpow_le_rpow_of_exponent_le hL hExp
  have hrow (z : A.State) :
      ∑' z', (A.physicalKernel true z z').re ≤ (L x) ^ Cabs := by
    by_cases hz : P.physical (J + F.ell) z.1 z.2
    · exact (physicalKernel_row_bound_of_C A x hP z.1 z.2 hz C hC hgroupBound).trans hbound
    · have hnot (π : P.Permutations (J + F.ell)) :
          ¬ P.physical (J + F.ell) z.1 (P.act π z.2) := by
        intro hact
        exact hz ((physical_act_iff π z.1 z.2).mp hact)
      have hzero (z' : A.State) : A.physicalKernel true z z' = 0 := by
        simp [Model.physicalKernel, Model.physicalRaw, hnot]
      simp [hzero]
      exact Real.rpow_nonneg hLpos.le _
  have hcol (z : A.State) :
      ∑' z', (A.physicalKernel true z' z).re ≤ (L x) ^ Cabs := by
    by_cases hz : P.physical (J + F.ell) z.1 z.2
    · exact (physicalKernel_column_bound_of_C A x hP z.1 z.2 hz C hC hgroupBound).trans hbound
    · have hnot (τ : P.Permutations (J + F.ell)) :
          ¬ P.physical (J + F.ell) z.1 (P.act τ z.2) := by
        intro hact
        exact hz ((physical_act_iff τ z.1 z.2).mp hact)
      have hzero (z' : A.State) : A.physicalKernel true z' z = 0 := by
        simp [Model.physicalKernel, Model.physicalRaw, hnot]
      simp [hzero]
      exact Real.rpow_nonneg hLpos.le _
  exact ⟨hrow, hcol⟩

example : Erdos821.Blueprint.Graph.physical_schur_statement :=
  @Erdos821.P3Core.physical_schur_proof

end Erdos821.P3Core
