import Erdos821.S56.BlueprintInvariant
import Erdos821.Leaves.MarkSup

/-! Removal of one designated small mark (paper eq. small-mark-removal).
Removing the designated slot of a small group is a bijection of ordered lists,
exact for every `n`; the residual list sum is a function of the cofactor alone
away from square multiples of the removed prime. -/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

variable {G : PrimeGroups} {t : Fin G.size → ℕ} {gs : Fin G.size}

/-- Residual admissibility: every slot except the designated one divides `k`. -/
def admR (G : PrimeGroups) (t : Fin G.size → ℕ) (gs : Fin G.size) (ls : Fin (t gs))
    (k : ℕ) (z : Tuple G t) : Prop :=
  (∀ g, Function.Injective (z g)) ∧ (∀ g, g ≠ gs → ∀ j, (z g j).val ∣ k) ∧
    (∀ j, j ≠ ls → (z gs j).val ∣ k)

/-- The residual list sum with the designated slot fixed to `p`. -/
def Wpre (G : PrimeGroups) (t : Fin G.size → ℕ) (gs : Fin G.size) (ls : Fin (t gs))
    (b : Tuple G t → ℂ) (k : ℕ) (p : Label G gs) : ℂ :=
  ∑ z, if z gs ls = p ∧ admR G t gs ls k z then b z else 0

theorem label_prime {g : Fin G.size} (p : Label G g) : p.val.Prime := G.prime g p.val p.2

theorem label_ne_of_ne_group {g h : Fin G.size} (hgh : g ≠ h) (p : Label G g) (q : Label G h) :
    p.val ≠ q.val := by
  intro heq
  have := Finset.disjoint_left.mp (G.disjoint g h hgh) p.2
  exact this (heq ▸ q.2)

theorem prime_dvd_div_of_ne {q p n : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p)
    (hpn : p ∣ n) (hqn : q ∣ n) : q ∣ n / p := by
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left _ hp.pos]
  rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h) hqp
  · exact h

theorem adm_iff_admR (ls : Fin (t gs)) (n : ℕ) (z : Tuple G t) :
    admissibleMarks G t n z ↔ ((z gs ls).val ∣ n ∧ admR G t gs ls (n / (z gs ls).val) z) := by
  constructor
  · intro hz
    have hp := hz gs
    refine ⟨hp.2 ls, fun g => (hz g).1, ?_, ?_⟩
    · intro g hg j
      exact prime_dvd_div_of_ne (label_prime _) (label_prime _)
        (label_ne_of_ne_group hg _ _) (hp.2 ls) ((hz g).2 j)
    · intro j hj
      have hne : (z gs j).val ≠ (z gs ls).val := fun h => hj (hp.1 (Subtype.ext h))
      exact prime_dvd_div_of_ne (label_prime _) (label_prime _) hne (hp.2 ls) (hp.2 j)
  · rintro ⟨hpn, hinj, hother, hgs⟩
    have hdiv : n / (z gs ls).val ∣ n := Nat.div_dvd_of_dvd hpn
    intro g
    refine ⟨hinj g, fun j => ?_⟩
    by_cases hg : g = gs
    · subst hg
      by_cases hj : j = ls
      · subst hj; exact hpn
      · exact (hgs j hj).trans hdiv
    · exact (hother g hg j).trans hdiv

/-- Exact removal of the designated slot, for every `n`. -/
theorem marks_sum_removal (ls : Fin (t gs)) (b : Tuple G t → ℂ) (n : ℕ) :
    (∑ z, if admissibleMarks G t n z then b z else 0) =
      ∑ p : Label G gs, if p.val ∣ n then Wpre G t gs ls b (n / p.val) p else 0 := by
  unfold Wpre
  have : ∀ p : Label G gs, (if p.val ∣ n then
      ∑ z, (if z gs ls = p ∧ admR G t gs ls (n / p.val) z then b z else 0) else 0) =
      ∑ z, if z gs ls = p ∧ (p.val ∣ n ∧ admR G t gs ls (n / p.val) z) then b z else 0 := by
    intro p
    split_ifs with h
    · apply Finset.sum_congr rfl; intro z _
      simp only [h, true_and]
    · symm; apply Finset.sum_eq_zero; intro z _
      simp only [h, false_and, and_false, if_false]
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (z gs ls)]
  · simp only [true_and]
    exact if_congr (adm_iff_admR ls n z) rfl rfl
  · intro p _ hp
    simp only [Ne.symm hp, false_and, if_false]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Changing the removed prime -/

/-- Replace the designated slot by `p`. -/
def swapS (ls : Fin (t gs)) (z : Tuple G t) (p : Label G gs) : Tuple G t :=
  Function.update z gs (Function.update (z gs) ls p)

theorem swapS_self (ls : Fin (t gs)) (z : Tuple G t) (p : Label G gs) :
    swapS ls z p gs ls = p := by
  simp [swapS]

theorem swapS_gs_ne (ls : Fin (t gs)) (z : Tuple G t) (p : Label G gs) {j : Fin (t gs)}
    (hj : j ≠ ls) : swapS ls z p gs j = z gs j := by
  simp [swapS, Function.update_of_ne hj]

theorem swapS_ne (ls : Fin (t gs)) (z : Tuple G t) (p : Label G gs) {g : Fin G.size}
    (hg : g ≠ gs) : swapS ls z p g = z g := by
  simp [swapS, Function.update_of_ne hg]

theorem swapS_swapS (ls : Fin (t gs)) (z : Tuple G t) (p : Label G gs) :
    swapS ls (swapS ls z p) (z gs ls) = z := by
  funext g
  by_cases hg : g = gs
  · subst hg
    funext j
    by_cases hj : j = ls
    · subst hj; rw [swapS_self]
    · rw [swapS_gs_ne ls _ _ hj, swapS_gs_ne ls _ _ hj]
  · rw [swapS_ne ls _ _ hg, swapS_ne ls _ _ hg]

theorem admR_swapS (ls : Fin (t gs)) (k : ℕ) (z : Tuple G t) (p : Label G gs)
    (hz : admR G t gs ls k z) (hp : ¬ p.val ∣ k) : admR G t gs ls k (swapS ls z p) := by
  obtain ⟨hinj, hother, hgs⟩ := hz
  refine ⟨?_, ?_, ?_⟩
  · intro g
    by_cases hg : g = gs
    · subst hg
      intro j1 j2 h12
      by_cases h1 : j1 = ls <;> by_cases h2 : j2 = ls
      · rw [h1, h2]
      · exfalso
        rw [h1, swapS_self, swapS_gs_ne ls _ _ h2] at h12
        exact hp (h12 ▸ hgs j2 h2)
      · exfalso
        rw [h2, swapS_self, swapS_gs_ne ls _ _ h1] at h12
        exact hp (h12 ▸ hgs j1 h1)
      · rw [swapS_gs_ne ls _ _ h1, swapS_gs_ne ls _ _ h2] at h12
        exact hinj _ h12
    · rw [swapS_ne ls _ _ hg]; exact hinj g
  · intro g hg j
    rw [swapS_ne ls _ _ hg]; exact hother g hg j
  · intro j hj
    rw [swapS_gs_ne ls _ _ hj]; exact hgs j hj

/-- With mark weights independent of small labels, the residual sum does not depend on
which removed prime (not dividing the cofactor) is used. -/
theorem Wpre_congr (ls : Fin (t gs)) (hgs : gs ∈ G.small) (b : Tuple G t → ℂ)
    (hb : ∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z')
    (k : ℕ) (p p' : Label G gs) (hp : ¬ p.val ∣ k) (hp' : ¬ p'.val ∣ k) :
    Wpre G t gs ls b k p = Wpre G t gs ls b k p' := by
  unfold Wpre
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hgsbig : gs ∉ G.big := by simp [PrimeGroups.big, hgs]
  have hbs : ∀ z q, b (swapS ls z q) = b z := by
    intro z q
    apply hb
    intro g hg
    have : g ≠ gs := fun h => hgsbig (h ▸ hg)
    rw [swapS_ne ls _ _ this]
  apply Finset.sum_nbij' (fun z => swapS ls z p') (fun z => swapS ls z p)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨swapS_self ls z p', admR_swapS ls k z p' hz.2 hp'⟩
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨swapS_self ls z p, admR_swapS ls k z p hz.2 hp⟩
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have := swapS_swapS ls z p'
    rw [hz.1] at this
    exact this
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have := swapS_swapS ls z p
    rw [hz.1] at this
    exact this
  · intro z _
    exact (hbs z p').symm

/-! ### The residual mark function -/

theorem dvd_mul_iff_of_prime_ne {q p m : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) :
    q ∣ p * m ↔ q ∣ m := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h) hqp
    · exact h
  · intro h; exact dvd_mul_of_dvd_right h p

/-- Removing a prime dividing `n` exactly once lowers `ω` by one. -/
theorem omega_mul_label (p : Label G gs) (m : ℕ) (hp : ¬ p.val ∣ m) :
    omega G (p.val * m) = omega G m + 1 := by
  unfold omega
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ gs),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ gs)]
  have hrest : ∑ g ∈ Finset.univ.erase gs, omegaGroup G g (p.val * m) =
      ∑ g ∈ Finset.univ.erase gs, omegaGroup G g m := by
    apply Finset.sum_congr rfl
    intro g hg
    have hg' : g ≠ gs := Finset.ne_of_mem_erase hg
    unfold omegaGroup
    congr 1
    apply Finset.filter_congr
    intro q hq
    exact dvd_mul_iff_of_prime_ne (G.prime g q hq) (label_prime p)
      (label_ne_of_ne_group hg' ⟨q, hq⟩ p)
  have hgs : omegaGroup G gs (p.val * m) = omegaGroup G gs m + 1 := by
    unfold omegaGroup
    have : (G.primes gs).filter (fun q => q ∣ p.val * m) =
        insert p.val ((G.primes gs).filter (fun q => q ∣ m)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hq, hdvd⟩
        by_cases hqp : q = p.val
        · left; exact hqp
        · right; exact ⟨hq, (dvd_mul_iff_of_prime_ne (G.prime gs q hq) (label_prime p) hqp).mp hdvd⟩
      · rintro (rfl | ⟨hq, hdvd⟩)
        · exact ⟨p.2, dvd_mul_right _ _⟩
        · exact ⟨hq, dvd_mul_of_dvd_right hdvd _⟩
    rw [this, Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, not_and]
    intro _; exact hp
  rw [hrest, hgs]
  ring

/-- The residual mark function of the cofactor. -/
def Wres (G : PrimeGroups) (t : Fin G.size → ℕ) (gs : Fin G.size) (ls : Fin (t gs))
    (q : ℝ) (b : Tuple G t → ℂ) (k : ℕ) : ℂ :=
  if h : ∃ p : Label G gs, ¬ p.val ∣ k then
    ((q ^ ((omega G k : ℤ) + 1 - ∑ g, (t g : ℤ)) * (∏ g, (mass G g)⁻¹ ^ t g) * mass G gs : ℝ) : ℂ) *
      Wpre G t gs ls b k (Classical.choose h)
  else 0

/-- The mark weight as a sum over the removed prime, exact for every `n`. -/
theorem weightedMarks_eq_removal (ls : Fin (t gs)) (q : ℝ) (b : Tuple G t → ℂ) (n : ℕ) :
    weightedMarks G q t b n = ∑ p : Label G gs, if p.val ∣ n then
      ((q ^ ((omega G n : ℤ) - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g : ℝ) : ℂ) *
        Wpre G t gs ls b (n / p.val) p else 0 := by
  unfold weightedMarks
  rw [marks_sum_removal ls b n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

/-- Away from square multiples of the removed prime, the term is the residual function. -/
theorem removal_term_eq (ls : Fin (t gs)) (hgs : gs ∈ G.small) (q : ℝ) (hq : 0 < q)
    (b : Tuple G t → ℂ) (hb : ∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z')
    (hmass : 0 < mass G gs) (p : Label G gs) (m : ℕ) (hp : ¬ p.val ∣ m) :
    ((q ^ ((omega G (p.val * m) : ℤ) - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g : ℝ) : ℂ) *
        Wpre G t gs ls b m p = ((mass G gs)⁻¹ : ℝ) * Wres G t gs ls q b m := by
  have h : ∃ p : Label G gs, ¬ p.val ∣ m := ⟨p, hp⟩
  unfold Wres
  rw [dif_pos h, Wpre_congr ls hgs b hb m (Classical.choose h) p (Classical.choose_spec h) hp,
    omega_mul_label p m hp]
  rw [← mul_assoc]
  congr 1
  have hm : (mass G gs : ℂ) ≠ 0 := by exact_mod_cast hmass.ne'
  push_cast
  rw [mul_comm ((mass G gs : ℂ))⁻¹, mul_inv_cancel_right₀ hm]

/-! ### Invariance under group-free factors and the sup bound -/

theorem label_dvd_mul_groupFree_iff {g : Fin G.size} (p : Label G g) {e k : ℕ}
    (he : S56Core.GroupFree G e) : p.val ∣ e * k ↔ p.val ∣ k := by
  have hpg : p.val ∈ S56Core.groupPrimes G := Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, p.2⟩
  constructor
  · intro h
    exact ((label_prime p).dvd_mul.mp h).resolve_left (he p.val hpg)
  · intro h; exact dvd_mul_of_dvd_right h e

theorem omega_mul_groupFree {e k : ℕ} (he : S56Core.GroupFree G e) : omega G (e * k) = omega G k := by
  unfold omega
  exact Finset.sum_congr rfl fun g _ => S56Core.omegaGroup_mul G e k he g

theorem admR_mul_groupFree (ls : Fin (t gs)) {e k : ℕ} (he : S56Core.GroupFree G e) (z : Tuple G t) :
    admR G t gs ls (e * k) z ↔ admR G t gs ls k z := by
  unfold admR
  simp only [label_dvd_mul_groupFree_iff _ he]

theorem Wpre_mul_groupFree (ls : Fin (t gs)) (b : Tuple G t → ℂ) {e k : ℕ}
    (he : S56Core.GroupFree G e) (p : Label G gs) :
    Wpre G t gs ls b (e * k) p = Wpre G t gs ls b k p := by
  unfold Wpre
  simp only [admR_mul_groupFree ls he]

theorem Wres_mul_groupFree (ls : Fin (t gs)) (hgs : gs ∈ G.small) (q : ℝ) (b : Tuple G t → ℂ)
    (hb : ∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z')
    {e k : ℕ} (he : S56Core.GroupFree G e) :
    Wres G t gs ls q b (e * k) = Wres G t gs ls q b k := by
  unfold Wres
  have hiff : (∃ p : Label G gs, ¬ p.val ∣ e * k) ↔ (∃ p : Label G gs, ¬ p.val ∣ k) := by
    simp only [label_dvd_mul_groupFree_iff _ he]
  by_cases h : ∃ p : Label G gs, ¬ p.val ∣ k
  · have h1 : ∃ p : Label G gs, ¬ p.val ∣ e * k := hiff.mpr h
    rw [dif_pos h1, dif_pos h, omega_mul_groupFree he, Wpre_mul_groupFree ls b he]
    congr 1
    apply Wpre_congr ls hgs b hb
    · have := Classical.choose_spec h1
      rwa [label_dvd_mul_groupFree_iff _ he] at this
    · exact Classical.choose_spec h
  · have h1 : ¬ ∃ p : Label G gs, ¬ p.val ∣ e * k := fun h' => h (hiff.mp h')
    rw [dif_neg h1, dif_neg h]

/-- The residual function is bounded by the marked sup bound. -/
theorem norm_Wres_le (P : Geometry) (tmax : ℕ) : ∃ C : ℝ, ∀ᶠ x in Filter.atTop,
    ∀ G : PrimeGroups, Admissible P x G →
      ∀ (t : Fin G.size → ℕ) (gs : Fin G.size) (ls : Fin (t gs)) (b : Tuple G t → ℂ),
        (∀ g, t g ≤ tmax) → (∀ z, ‖b z‖ ≤ 1) →
        ∀ k, ‖Wres G t gs ls P.q b k‖ ≤ mass G gs * L x ^ C := by
  obtain ⟨C, hC⟩ := mark_sup P tmax
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  intro G hG t gs ls b htm hb1 k
  have hmass : 0 < mass G gs := P.positive.2.2.1.trans_le (hG.2.2.1 gs).1
  have hq : 0 < P.q := P.damping.1
  have hLC : 0 ≤ L x ^ C := by
    have := hx G hG t (fun _ => 1) 1 htm zero_le_one (fun _ => by simp) 0
    exact (norm_nonneg _).trans (by simpa using this)
  unfold Wres
  by_cases h : ∃ p : Label G gs, ¬ p.val ∣ k
  · rw [dif_pos h]
    set p := Classical.choose h with hpdef
    have hp : ¬ p.val ∣ k := Classical.choose_spec h
    set A := (Finset.univ : Finset (Tuple G t)).filter
      (fun z => z gs ls = p ∧ admR G t gs ls k z) with hA
    set A' := (Finset.univ : Finset (Tuple G t)).filter
      (fun z => admissibleMarks G t (p.val * k) z) with hA'
    have hWpre : ‖Wpre G t gs ls b k p‖ ≤ A.card := by
      unfold Wpre
      rw [← Finset.sum_filter]
      calc ‖∑ z ∈ A, b z‖ ≤ ∑ z ∈ A, ‖b z‖ := norm_sum_le _ _
        _ ≤ ∑ _z ∈ A, (1 : ℝ) := Finset.sum_le_sum fun z _ => hb1 z
        _ = A.card := by simp
    have hAA : A.card ≤ A'.card := by
      apply Finset.card_le_card
      intro z hz
      simp only [hA, hA', Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [adm_iff_admR ls, hz.1]
      refine ⟨dvd_mul_right _ _, ?_⟩
      rw [Nat.mul_div_cancel_left _ (label_prime p).pos]
      exact hz.2
    have hwm := hx G hG t (fun _ => 1) 1 htm zero_le_one (fun _ => by simp) (p.val * k)
    have hwmeq : weightedMarks G P.q t (fun _ => 1) (p.val * k) =
        ((P.q ^ ((omega G k : ℤ) + 1 - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g : ℝ) : ℂ) *
          (A'.card : ℂ) := by
      unfold weightedMarks
      rw [omega_mul_label p k hp]
      congr 1
      rw [Finset.sum_boole]
    rw [hwmeq, one_mul] at hwm
    have hcoef : 0 ≤ P.q ^ ((omega G k : ℤ) + 1 - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g := by
      apply mul_nonneg (zpow_nonneg hq.le _)
      exact Finset.prod_nonneg fun g _ => pow_nonneg (inv_nonneg.mpr
        (P.positive.2.2.1.le.trans (hG.2.2.1 g).1)) _
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcoef] at hwm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcoef hmass.le)]
    calc (P.q ^ ((omega G k : ℤ) + 1 - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g) * mass G gs *
          ‖Wpre G t gs ls b k p‖
        ≤ (P.q ^ ((omega G k : ℤ) + 1 - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g) * mass G gs *
          A'.card := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcoef hmass.le)
          exact hWpre.trans (by exact_mod_cast hAA)
      _ = mass G gs * ((P.q ^ ((omega G k : ℤ) + 1 - ∑ g, (t g : ℤ)) *
          ∏ g, (mass G g)⁻¹ ^ t g) * A'.card) := by ring
      _ ≤ mass G gs * L x ^ C := mul_le_mul_of_nonneg_left hwm hmass.le
  · rw [dif_neg h, norm_zero]
    exact mul_nonneg hmass.le hLC

end Erdos821.P5Marked
