import Erdos408.Graph.Labels

/-!
# One pattern of the physical operator

For one pattern `ν` of an upstream model with `k = 1`, the pairing of its term
of `physicalRaw` (`patternRaw`), between endpoints of the position alone, is
`GraphTransference`'s `patternPairing` (`rawPairing_eq`). Term by term:

* upstream physical states, compatibility, the ban, and `D` are the
  conditions and edge product of `patternPairing` on the label values;
* the state mass `∏ V_g^{-M}` and target mass `∏ V_g^{-t_g}` are its weights,
  and the auxiliary mass integrates out the unchanged slots (`sum_trim`);
* the damping `q^{(ω(n) - M s)/2}` is `√q^{ω(n) - M s}`, as `ω(n) ≥ M s` on
  physical states;
* `imaginaryPower D ζ` is `D^{iζ}`, as `D ≥ 1`;
* the target position `n' = n + D` is the only one in the sum over `S'` that
  contributes, and it lies in `S'` unless `g` vanishes there.
-/

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph
open scoped Classical

variable {G : PrimeGroups}

/-! ### Upstream conditions on label values -/

section Conditions

variable {M J m : ℕ}

/-- An upstream state is physical when the label values are. -/
lemma physical_iff (n : ℕ) (a : G.Labels M) :
    G.physical M (n : ℤ) a ↔ ∀ g, Function.Injective (vals a g) ∧ ∀ i, vals a g i ∣ n := by
  refine forall_congr' fun g => and_congr ?_ (forall_congr' fun _ => Int.natCast_dvd_natCast)
  exact (Function.Injective.of_comp_iff Subtype.val_injective (a g)).symm

/-- Upstream compatibility: the label values agree in the shared slots. -/
lemma compatible_iff (ν : Pattern G J 1 m) (a b : G.Labels (J + 1)) :
    ν.compatible a b ↔
      ∀ g, ∀ i : Fin J, i ∉ ν.changed g → vals b g i.castSucc = vals a g i.castSucc := by
  constructor
  · intro h g i hi
    exact congrArg Subtype.val (h g i.castSucc ⟨i, rfl, hi⟩).symm
  · rintro h g _ ⟨j, rfl, hj⟩
    exact Subtype.ext (h g j hj).symm

/-- The upstream ban: the trimmed auxiliary values avoid both lists. -/
lemma ban_iff (ν : Pattern G J 1 m) (a b : G.Labels (J + 1)) (u : G.Aux J) :
    ν.ban a b u ↔ ∀ g, ∀ i ∈ ν.changed g, ∀ j,
      trim ν.changed u g i ≠ vals a g j ∧ trim ν.changed u g i ≠ vals b g j := by
  refine forall_congr' fun g => forall_congr' fun i => forall_congr' fun hi =>
    forall_congr' fun j => ?_
  rw [show trim ν.changed u g i = (u g i).val from ite_eq_left hi]
  exact and_congr (not_congr Subtype.ext_iff) (not_congr Subtype.ext_iff)

/-- Upstream's `D` is the edge product of the label values. -/
lemma D_eq (ν : Pattern G J 1 m) (a : G.Labels (J + 1)) (u : G.Aux J) :
    ν.D a u = edgeProduct ν.changed (vals a) (trim ν.changed u) := by
  simp only [Pattern.D, edgeProduct]
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ ν.changed g
  · simp [trim, hi]
  · simp only [hi, ite_false, vals]
    rfl

/-- The edge product of upstream labels is positive. -/
lemma edgeProduct_pos {C : Fin G.count → Finset (Fin J)} (a : G.Labels (J + 1))
    (u : G.Aux J) : 0 < edgeProduct C (vals a) (trim C u) := by
  refine Finset.prod_pos fun g _ => Finset.prod_pos fun i _ => ?_
  by_cases hi : i ∈ C g
  · simp only [trim, hi, ite_true]
    exact (G.prime g _ (u g i).property).pos
  · simp only [hi, ite_false]
    exact (G.prime g _ (a g i.castSucc).property).pos

/-- Upstream's `ω` is `groupPrimeCount`. -/
lemma omega_eq (n : ℕ) : G.omega (n : ℤ) = groupPrimeCount G.primes n := by
  simp only [PrimeGroups.omega, PrimeGroups.omegaGroup, groupPrimeCount, primeCount,
    Int.natCast_dvd_natCast]

/-- On physical lists, `ω(n) ≥ M s`. -/
lemma le_groupPrimeCount {ι : Type*} [Fintype ι] {P : ι → Finset ℕ} {n : ℕ}
    {p : ι → Fin M → ℕ} (hmem : ∀ g i, p g i ∈ P g)
    (hp : ∀ g, Function.Injective (p g) ∧ ∀ i, p g i ∣ n) :
    M * Fintype.card ι ≤ groupPrimeCount P n := by
  rw [groupPrimeCount, mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_le_sum fun g _ => ?_
  have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin M)))
    (t := (P g).filter (· ∣ n)) (p g)
    (fun i _ => Finset.mem_filter.mpr ⟨hmem g i, (hp g).2 i⟩) ((hp g).1.injOn)
  simpa [primeCount] using this

/-- On physical states, upstream's damping is `√q₀^{ω(n) - M s}`. -/
lemma damping_eq {F : FixedData} (hF : F.ell = 1) (A : Model F G J m) (n : ℕ)
    (hn : (J + 1) * G.count ≤ groupPrimeCount G.primes n) :
    A.damping (n : ℤ) = Real.sqrt F.q ^ (groupPrimeCount G.primes n - (J + 1) * G.count) := by
  rw [Model.damping, omega_eq, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul F.q_pos.le, Nat.cast_sub hn, hF]
  push_cast
  ring_nf

end Conditions

/-! ### One pattern of upstream's pairing -/

/-- The term of pattern `v` in upstream's `physicalRaw false`. -/
noncomputable def patternRaw {F : FixedData} {J m : ℕ} (A : Model F G J m)
    (v : Fin A.patternCount) (z z' : A.State) : ℂ :=
  if G.physical (J + F.ell) z.1 z.2 ∧ G.physical (J + F.ell) z'.1 z'.2 then
    ∑ u : G.Aux J,
      if (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
          z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
        ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass * A.damping z.1 *
            A.damping z'.1 : ℝ) *
          ((A.pattern v).coefficient (G.restrictBig z.2) (G.restrictBig z'.2)
              (fun g => u g.val) *
            imaginaryPower ((A.pattern v).D z.2 u) A.zeta)
      else 0
  else 0

/-- Upstream's `physicalRaw false` is the sum of its pattern terms. -/
lemma physicalRaw_eq_sum {F : FixedData} {J m : ℕ} (A : Model F G J m) (z z' : A.State) :
    A.physicalRaw false z z' = ∑ v, patternRaw A v z z' := by
  unfold Model.physicalRaw patternRaw
  simp only [Bool.false_eq_true, ite_false]
  split_ifs <;> simp

/-- The pairing of pattern `v`'s term between `f` on `S` and `g` on `S'`, as a
sum over states. -/
noncomputable def rawPairing {F : FixedData} {J m : ℕ} (A : Model F G J m)
    (v : Fin A.patternCount) (S S' : Finset ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ n' ∈ S', ∑ b : G.Labels (J + F.ell),
    (A.stateMass ((n : ℤ), a) : ℂ) * star (f n) *
      patternRaw A v ((n : ℤ), a) ((n' : ℤ), b) * g n'

/-! ### `patternPairing` as a sum over all lists -/

/-- The summand of `patternPairing` at source `(n, p)`, target list `p'` and
auxiliary labels `a`, without the auxiliary mass, and `0` off its support. -/
noncomputable def pairTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (q₀ : ℝ) {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) (ζ : ℝ)
    (f g : ℕ → ℂ) (n : ℕ) (p p' : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) : ℂ :=
  if (∀ h, Function.Injective (p h) ∧ ∀ i, p h i ∣ n) ∧
      (∀ h, Function.Injective (p' h) ∧ ∀ i, p' h i ∣ n + edgeProduct C p a) ∧
      ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
        ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j then
    ((∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) * (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) :
        ℝ) : ℂ) *
      starRingEnd ℂ (f n) * K p p' a * ((edgeProduct C p a : ℂ) ^ ((ζ : ℂ) * Complex.I)) *
      ((Real.sqrt q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
        Real.sqrt q₀ ^ (groupPrimeCount P (n + edgeProduct C p a) -
          (J + 1) * Fintype.card ι) : ℝ) : ℂ) *
      g (n + edgeProduct C p a)
  else 0

/-- `patternPairing` sums `pairTerm` against the auxiliary mass over all lists
and auxiliary labels. -/
lemma patternPairing_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (q₀ : ℝ) {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) (ζ : ℝ)
    (S : Finset ℕ) (f g : ℕ → ℂ) :
    patternPairing P q₀ C K ζ S f g =
      ∑ n ∈ S, ∑ p ∈ Fintype.piFinset (fun h => Fintype.piFinset fun _ : Fin (J + 1) => P h),
        ∑ a ∈ auxLabels P C,
          ∑ p' ∈ Fintype.piFinset (fun h => Fintype.piFinset fun _ : Fin (J + 1) => P h),
            pairTerm P q₀ C K ζ f g n p p' a *
              ((∏ h, ∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹ : ℝ) : ℂ) := by
  unfold patternPairing physicalLists
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ∀ h, Function.Injective (p h) ∧ ∀ i, p h i ∣ n
  · rw [ite_eq_left hp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.filter_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p' _ => ?_
    unfold pairTerm
    by_cases hp' : (∀ h, Function.Injective (p' h) ∧ ∀ i, p' h i ∣ n + edgeProduct C p a) ∧
        ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
          ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j
    · rw [ite_eq_left hp', ite_eq_left ⟨hp, hp'⟩]
      simp only [Finset.prod_mul_distrib]
      push_cast
      ring
    · rw [ite_eq_right hp', ite_eq_right fun h => hp' h.2, zero_mul]
  · rw [ite_eq_right hp]
    refine (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun p' _ => ?_).symm
    unfold pairTerm
    rw [ite_eq_right fun h => hp h.1, zero_mul]

/-- Summing over upstream labels and auxiliary labels against the auxiliary
mass is summing over lists and `auxLabels` against the free-slot mass. -/
lemma sum_labels_aux {J : ℕ} (C : Fin G.count → Finset (Fin J)) (hV : ∀ g, G.V g ≠ 0)
    (Φ : (Fin G.count → Fin (J + 1) → ℕ) → (Fin G.count → Fin (J + 1) → ℕ) →
      (Fin G.count → Fin J → ℕ) → ℂ) :
    ∑ a : G.Labels (J + 1), ∑ b : G.Labels (J + 1), ∑ u : G.Aux J,
        Φ (vals a) (vals b) (trim C u) * ((∏ g, ∏ i, G.mu g (u g i) : ℝ) : ℂ) =
      ∑ p ∈ Fintype.piFinset (fun h => Fintype.piFinset fun _ : Fin (J + 1) => G.primes h),
        ∑ w ∈ auxLabels G.primes C,
          ∑ p' ∈ Fintype.piFinset (fun h => Fintype.piFinset fun _ : Fin (J + 1) => G.primes h),
            Φ p p' w * ((∏ h, ∏ i ∈ C h, (harmonicMass (G.primes h) * w h i)⁻¹ : ℝ) : ℂ) := by
  calc _ = ∑ a : G.Labels (J + 1), ∑ b : G.Labels (J + 1), ∑ w ∈ auxLabels G.primes C,
          Φ (vals a) (vals b) w *
            ((∏ h, ∏ i ∈ C h, (harmonicMass (G.primes h) * w h i)⁻¹ : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          sum_trim C hV (Φ (vals a) (vals b))
    _ = ∑ a : G.Labels (J + 1), ∑ w ∈ auxLabels G.primes C, ∑ b : G.Labels (J + 1),
          Φ (vals a) (vals b) w *
            ((∏ h, ∏ i ∈ C h, (harmonicMass (G.primes h) * w h i)⁻¹ : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Eq.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ =>
          sum_vals fun p' => Φ (vals a) p' w *
            ((∏ h, ∏ i ∈ C h, (harmonicMass (G.primes h) * w h i)⁻¹ : ℝ) : ℂ)) ?_
        exact sum_vals fun p => ∑ w ∈ auxLabels G.primes C,
          ∑ p' ∈ Fintype.piFinset (fun h => Fintype.piFinset fun _ : Fin (J + 1) => G.primes h),
            Φ p p' w * ((∏ h, ∏ i ∈ C h, (harmonicMass (G.primes h) * w h i)⁻¹ : ℝ) : ℂ)

/-! ### Weights -/

/-- `imaginaryPower D ζ` is `D^{iζ}` for `D ≠ 0`. -/
lemma imaginaryPower_eq {D : ℕ} (hD : D ≠ 0) (ζ : ℝ) :
    imaginaryPower D ζ = (D : ℂ) ^ ((ζ : ℂ) * Complex.I) := by
  rw [imaginaryPower, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hD),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  ring_nf

/-- The mark mass `∏ V_g^{-M}`. -/
lemma markMass_eq (M : ℕ) : G.markMass M = ∏ g, (harmonicMass (G.primes g))⁻¹ ^ M := by
  simp [PrimeGroups.markMass, V_eq_harmonicMass, zpow_neg, inv_pow]

/-- The physical target mass `∏ V_g^{-t_g}`, `t_g = |C g| + 1`. -/
lemma physicalTargetMass_eq {J m : ℕ} (ν : Pattern G J 1 m) :
    ν.physicalTargetMass = ∏ g, (harmonicMass (G.primes g))⁻¹ ^ ((ν.changed g).card + 1) := by
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Pattern.t, V_eq_harmonicMass, zpow_neg, zpow_natCast, inv_pow, add_comm]

/-! ### The identity -/

section Identity

variable {q₀ c₀ C₀ vlo vhi : ℝ} {hq₀ : 0 < q₀} {hq₁ : q₀ < 1} {hc₀ : 0 < c₀} {hvlo : 0 < vlo}
  {J m : ℕ}

/-- Upstream physical lists have `ω(n) ≥ M s`. -/
lemma le_groupPrimeCount_of_physical {M n : ℕ} {a : G.Labels M}
    (h : G.physical M (n : ℤ) a) : M * G.count ≤ groupPrimeCount G.primes n := by
  have := le_groupPrimeCount (P := G.primes) (fun g i => (a g i).property)
    ((physical_iff n a).mp h)
  rwa [Fintype.card_fin] at this

/-- The pairing of pattern `v`'s term is `patternPairing` with its changed
slots, for a kernel `K` that agrees with its coefficient on label values, when
`g` vanishes off `S'`. -/
theorem rawPairing_eq (B : Family (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) G J m)
    (ζ : ℝ) (v : Fin B.count)
    (K : (Fin G.count → Fin (J + 1) → ℕ) → (Fin G.count → Fin (J + 1) → ℕ) →
      (Fin G.count → Fin J → ℕ) → ℂ)
    (hK : ∀ a b u, (B.pattern v).coefficient (G.restrictBig a) (G.restrictBig b)
      (fun g => u g.val) = K (vals a) (vals b) (trim (B.pattern v).changed u))
    (hV : ∀ g, G.V g ≠ 0) (S S' : Finset ℕ) (f g : ℕ → ℂ) (hg : ∀ n ∉ S', g n = 0) :
    rawPairing (B.model 1 ζ) v S S' f g =
      patternPairing G.primes q₀ (B.pattern v).changed K ζ S f g := by
  rw [patternPairing_eq_sum]
  unfold rawPairing
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← sum_labels_aux (B.pattern v).changed hV
    (pairTerm G.primes q₀ (B.pattern v).changed K ζ f g n)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- expand the pattern term over the auxiliary labels
  have hraw : ∀ n' : ℕ, patternRaw (B.model 1 ζ) v ((n : ℤ), a) ((n' : ℤ), b) =
      ∑ u : G.Aux J,
        if G.physical (J + 1) (n : ℤ) a ∧ G.physical (J + 1) (n' : ℤ) b then
          (if (B.pattern v).compatible a b ∧ (B.pattern v).ban a b u ∧
              (n' : ℤ) = n + 1 * ((B.pattern v).D a u : ℤ) then
            (((B.pattern v).auxMass u * (B.pattern v).physicalTargetMass *
                (B.model 1 ζ).damping n * (B.model 1 ζ).damping n' : ℝ) : ℂ) *
              ((B.pattern v).coefficient (G.restrictBig a) (G.restrictBig b)
                  (fun g => u g.val) *
                imaginaryPower ((B.pattern v).D a u) ζ)
          else 0)
        else 0 := by
    intro n'
    unfold patternRaw
    split_ifs <;> simp [Family.model]
  simp_rw [hraw, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hE := D_eq (B.pattern v) a u
  set N := n + edgeProduct (B.pattern v).changed (vals a) (trim (B.pattern v).changed u)
    with hN
  rw [Finset.sum_eq_single N (fun n' _ hn' => ?_) (fun hN' => ?_)]
  · unfold pairTerm
    have hiff : ((∀ h, Function.Injective (vals a h) ∧ ∀ i, vals a h i ∣ n) ∧
        (∀ h, Function.Injective (vals b h) ∧ ∀ i, vals b h i ∣ N) ∧
        ∀ h, (∀ i, i ∉ (B.pattern v).changed h → vals b h i.castSucc = vals a h i.castSucc) ∧
          ∀ i ∈ (B.pattern v).changed h, ∀ j, trim (B.pattern v).changed u h i ≠ vals a h j ∧
            trim (B.pattern v).changed u h i ≠ vals b h j) ↔
        G.physical (J + 1) (n : ℤ) a ∧ G.physical (J + 1) (N : ℤ) b ∧
          (B.pattern v).compatible a b ∧ (B.pattern v).ban a b u := by
      rw [physical_iff, physical_iff, compatible_iff, ban_iff]
      exact and_congr Iff.rfl (and_congr Iff.rfl forall_and)
    by_cases hc : G.physical (J + 1) (n : ℤ) a ∧ G.physical (J + 1) (N : ℤ) b ∧
        (B.pattern v).compatible a b ∧ (B.pattern v).ban a b u
    · rw [ite_eq_left ⟨hc.1, hc.2.1⟩,
        ite_eq_left ⟨hc.2.2.1, hc.2.2.2, by rw [hE, hN]; push_cast; ring⟩,
        ite_eq_left (hiff.mpr hc), Model.stateMass, ite_eq_left hc.1,
        damping_eq rfl _ n (le_groupPrimeCount_of_physical hc.1),
        damping_eq rfl _ N (le_groupPrimeCount_of_physical hc.2.1), hK,
        imaginaryPower_eq (by rw [hE]; exact (edgeProduct_pos a u).ne'), hE, markMass_eq,
        physicalTargetMass_eq, Fintype.card_fin]
      simp only [Pattern.auxMass, Finset.prod_mul_distrib, starRingEnd_apply]
      push_cast
      ring
    · rw [ite_eq_right (mt hiff.mp hc), zero_mul]
      split_ifs with h₁ h₂
      · exact absurd ⟨h₁.1, h₁.2, h₂.1, h₂.2.1⟩ hc
      all_goals simp
  · split_ifs with h₁ h₂
    · exact absurd h₂.2.2 (by rw [hE]; rw [hN] at hn'; omega)
    all_goals simp
  · rw [hg N hN', mul_zero]

end Identity

end Erdos408.Graph
