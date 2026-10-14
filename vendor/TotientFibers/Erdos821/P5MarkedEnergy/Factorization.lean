import Erdos821.P5MarkedEnergy.MarkRemoval
import Erdos821.S56.GroupParts
import Erdos821.P5.EndpointInvariance
import Erdos821.P5.EndpointBounds

/-! The full integer factorization `w = m p_s p r` of a marked endpoint (paper
§4, four-factor endpoint): the endpoint times the residual mark sum is a
four-fold Dirichlet convolution. -/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- Three-fold convolution with variables in `[1, N]`. -/
def tri (f1 f3 f4 : ℕ → ℂ) (N k : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
    if m * p * r = k then f1 m * f3 p * f4 r else 0

/-- Four-fold convolution with variables in `[1, N]`. -/
def quad (f1 f2 f3 f4 : ℕ → ℂ) (N n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N, ∑ p ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
    if m * s * p * r = n then f1 m * f2 s * f3 p * f4 r else 0

theorem quad_eq_sum_tri (f1 f2 f3 f4 : ℕ → ℂ) (N n : ℕ) :
    quad f1 f2 f3 f4 N n =
      ∑ s ∈ Finset.Icc 1 N, f2 s * (if s ∣ n then tri f1 f3 f4 N (n / s) else 0) := by
  unfold quad tri
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  split_ifs with hsn
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    obtain ⟨c, rfl⟩ := hsn
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hiff : m * s * p * r = s * c ↔ m * p * r = c := by
      constructor
      · intro h
        apply Nat.eq_of_mul_eq_mul_left (show 0 < s by omega)
        rw [← h]; ring
      · intro h; rw [← h]; ring
    by_cases h : m * p * r = c
    · rw [if_pos (hiff.mpr h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  · rw [mul_zero]
    apply Finset.sum_eq_zero; intro m _
    apply Finset.sum_eq_zero; intro p _
    apply Finset.sum_eq_zero; intro r _
    rw [if_neg]
    intro h
    exact hsn ⟨m * p * r, by rw [← h]; ring⟩

/-! ### Group-part facts -/

theorem groupFree_of_dvd {G : PrimeGroups} {d n : ℕ} (hn : S56Core.GroupFree G n) (hd : d ∣ n) :
    S56Core.GroupFree G d := fun p hp hpd => hn p hp (hpd.trans hd)

theorem groupPart_primeFactors (G : PrimeGroups) (n : ℕ) :
    (S56Core.groupPart G n).primeFactors ⊆ Finset.univ.biUnion G.primes := by
  unfold S56Core.groupPart
  apply P5Core.primeFactors_prod_supported
  · intro p hp
    exact pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_inter.mp hp).1) _
  · intro p hp q hq
    have hp' := (Finset.mem_inter.mp hp)
    have hqp : q = p := by
      have hqprime := Nat.prime_of_mem_primeFactors hq
      have hqdvd := Nat.dvd_of_mem_primeFactors hq
      exact (Nat.prime_dvd_prime_iff_eq hqprime (Nat.prime_of_mem_primeFactors hp'.1)).mp
        (hqprime.dvd_of_dvd_pow hqdvd)
    rw [hqp]; exact hp'.2

theorem groupFreePart_groupPart_mul (G : PrimeGroups) (n r : ℕ) :
    groupFreePart G (S56Core.groupPart G n * r) = groupFreePart G r :=
  P5Core.groupFreePart_mul_supported G _ r (S56Core.groupPart_pos G n).ne'
    (groupPart_primeFactors G n)

/-! ### Endpoint coefficient functions -/

/-- The `m` coefficient. -/
def A0 (E : Endpoint) (m : ℕ) : ℂ :=
  E.alpha m * E.chi (m : ZMod E.modulus) * Blueprint.Analytic.mellin m E.sigma₀

/-- The rough long-factor coefficient. -/
def P0 (E : Endpoint) (x : ℝ) (p : ℕ) : ℂ :=
  if E.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ E.hi ∧ rough (W x) p then Blueprint.Analytic.mellin p E.sigma₁ else 0

theorem endpoint_eq_triples (G : PrimeGroups) (x : ℝ) (E : Endpoint) (n : ℕ) :
    endpoint G x E n = ∑ u ∈ P5Core.factorTriples (groupFreePart G n),
      A0 E u.1 * P0 E x u.2.1 * E.residual u.2.2 := by
  rw [P5Core.endpoint_factorization]
  apply Finset.sum_congr rfl
  intro u _
  unfold A0 P0
  split_ifs <;> ring

theorem endpoint_mul_supported (G : PrimeGroups) (x : ℝ) (E : Endpoint) (D n : ℕ) (hD : D ≠ 0)
    (hprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes) :
    endpoint G x E (D * n) = endpoint G x E n := by
  unfold endpoint
  rw [P5Core.groupFreePart_mul_supported G D n hD hprime]

/-- The three-fold identity: endpoint times an invariant residual function. -/
theorem endpoint_mul_eq_tri (G : PrimeGroups) (x : ℝ) (E : Endpoint) (Wr : ℕ → ℂ)
    (hfree : ∀ m, rough (W x) m → S56Core.GroupFree G m)
    (hαrough : ∀ m, E.alpha m ≠ 0 → rough (W x) m)
    (hinv : ∀ e k, S56Core.GroupFree G e → Wr (e * k) = Wr k)
    (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    endpoint G x E k * Wr k =
      tri (A0 E) (P0 E x) (fun r => E.residual (groupFreePart G r) * Wr r) N k := by
  set R0 : ℕ → ℂ := fun r => E.residual (groupFreePart G r) * Wr r with hR0
  have hA0 : ∀ m, A0 E m ≠ 0 → S56Core.GroupFree G m := by
    intro m hm
    apply hfree
    apply hαrough
    intro h; apply hm; simp [A0, h]
  have hP0 : ∀ p, P0 E x p ≠ 0 → S56Core.GroupFree G p := by
    intro p hp
    apply hfree
    unfold P0 at hp
    split_ifs at hp with h
    · exact h.2.2
    · exact absurd rfl hp
  rw [endpoint_eq_triples, Finset.sum_mul]
  set gk := groupFreePart G k with hgk
  set pk := S56Core.groupPart G k with hpk
  have hkfac : pk * gk = k := S56Core.groupPart_mul_freePart G k (by omega)
  have hgkpos : 0 < gk := S56Core.groupFreePart_pos G k
  have hpkpos : 0 < pk := S56Core.groupPart_pos G k
  have hgkfree : S56Core.GroupFree G gk := S56Core.groupFreePart_groupFree G k
  -- the right side as a sum over filtered triples
  have hrhs : tri (A0 E) (P0 E x) R0 N k = ∑ v ∈ ((Finset.Icc 1 N ×ˢ (Finset.Icc 1 N ×ˢ
      Finset.Icc 1 N)).filter (fun v : ℕ × ℕ × ℕ => v.1 * v.2.1 * v.2.2 = k)),
      A0 E v.1 * P0 E x v.2.1 * R0 v.2.2 := by
    unfold tri
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_product]
  rw [hrhs]
  apply Finset.sum_bij_ne_zero (fun u _ _ => (u.1, u.2.1, k / (u.1 * u.2.1)))
  · intro u hu hne
    obtain ⟨hm, hp, hr, hprod⟩ := P5Core.factorTriples_info gk u hu
    have hkdiv : k = u.1 * u.2.1 * (u.2.2 * pk) := by rw [← hkfac, ← hprod]; ring
    have hq : k / (u.1 * u.2.1) = u.2.2 * pk := by
      rw [hkdiv]; exact Nat.mul_div_cancel_left _ (by positivity)
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    rw [hq]
    have hle : u.2.2 * pk ≤ k := by
      rw [hkdiv]; apply Nat.le_mul_of_pos_left; positivity
    refine ⟨⟨⟨hm, ?_⟩, ⟨hp, ?_⟩, ⟨Nat.mul_pos hr hpkpos, hle.trans hkN⟩⟩, by rw [← hkdiv]⟩
    · have : u.1 ≤ k := by
        calc u.1 ≤ u.1 * (u.2.1 * (u.2.2 * pk)) := Nat.le_mul_of_pos_right _ (by positivity)
          _ = k := by rw [hkdiv]; ring
      omega
    · have : u.2.1 ≤ k := by
        calc u.2.1 ≤ u.1 * u.2.1 := Nat.le_mul_of_pos_left _ hm
          _ ≤ u.1 * u.2.1 * (u.2.2 * pk) := Nat.le_mul_of_pos_right _ (by positivity)
          _ = k := hkdiv.symm
      omega
  · intro u hu _ u' hu' _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2, _⟩ := heq
    obtain ⟨hm, hp, _, hprod⟩ := P5Core.factorTriples_info gk u hu
    obtain ⟨_, _, _, hprod'⟩ := P5Core.factorTriples_info gk u' hu'
    have h3 : u.2.2 = u'.2.2 := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < u.1 * u.2.1 by positivity)
      rw [hprod, h1, h2, hprod']
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro v hv hne
    obtain ⟨⟨⟨hv1, _⟩, ⟨hv2, _⟩, ⟨hv3, _⟩⟩, hvprod⟩ := by
      simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] using hv
    have hA : A0 E v.1 ≠ 0 := fun h => hne (by rw [h]; ring)
    have hP : P0 E x v.2.1 ≠ 0 := fun h => hne (by rw [h]; ring)
    have hf1 := hA0 _ hA
    have hf2 := hP0 _ hP
    have hgk' : gk = v.1 * v.2.1 * groupFreePart G v.2.2 := by
      rw [hgk, ← hvprod, mul_assoc, S56Core.groupFreePart_mul G _ _ (by omega) (by positivity) hf1,
        S56Core.groupFreePart_mul G _ _ (by omega) (by omega) hf2, mul_assoc]
    have hWk : Wr k = Wr v.2.2 := by
      rw [← hvprod, mul_assoc, hinv _ _ hf1, hinv _ _ hf2]
    have hgpos := S56Core.groupFreePart_pos G v.2.2
    refine ⟨(v.1, v.2.1, groupFreePart G v.2.2), ?_, ?_, ?_⟩
    · unfold P5Core.factorTriples
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hv1, ?_⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hv2, ?_⟩, Finset.mem_Icc.mpr ⟨hgpos, ?_⟩⟩⟩,
        hgk'.symm⟩
      · rw [hgk', mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
      · rw [hgk']
        calc v.2.1 ≤ v.1 * v.2.1 := Nat.le_mul_of_pos_left _ hv1
          _ ≤ _ := Nat.le_mul_of_pos_right _ hgpos
      · rw [hgk']; exact Nat.le_mul_of_pos_left _ (by positivity)
    · simp only
      rw [hWk]
      simpa [hR0, mul_assoc] using hne
    · have h3 : v.1 * v.2.1 * v.2.2 / (v.1 * v.2.1) = v.2.2 :=
        Nat.mul_div_cancel_left _ (by positivity)
      simp only
      rw [← hvprod, h3]
  · intro u hu _
    obtain ⟨hm, hp, hr, hprod⟩ := P5Core.factorTriples_info gk u hu
    have hkdiv : k = u.1 * u.2.1 * (u.2.2 * pk) := by rw [← hkfac, ← hprod]; ring
    have hq : k / (u.1 * u.2.1) = u.2.2 * pk := by
      rw [hkdiv]; exact Nat.mul_div_cancel_left _ (by positivity)
    simp only [hR0]
    rw [hq]
    by_cases hz : A0 E u.1 * P0 E x u.2.1 = 0
    · rw [hz]; ring
    · have hA : A0 E u.1 ≠ 0 := fun h => hz (by rw [h]; ring)
      have hP : P0 E x u.2.1 ≠ 0 := fun h => hz (by rw [h]; ring)
      have hf1 := hA0 _ hA
      have hf2 := hP0 _ hP
      have hu3free : S56Core.GroupFree G u.2.2 :=
        groupFree_of_dvd hgkfree ⟨u.1 * u.2.1, by rw [← hprod]; ring⟩
      have hg3 : groupFreePart G (u.2.2 * pk) = u.2.2 := by
        rw [mul_comm, groupFreePart_groupPart_mul, S56Core.groupFreePart_eq_self G _ hr hu3free]
      have hW3 : Wr k = Wr (u.2.2 * pk) := by
        rw [hkdiv, mul_assoc, hinv _ _ hf1, hinv _ _ hf2]
      rw [hg3, hW3]
      ring

/-! ### The four-fold identity -/

/-- The small-prime coefficient. -/
def S0 (G : PrimeGroups) (gs : Fin G.size) (s : ℕ) : ℂ :=
  if s ∈ G.primes gs then ((mass G gs)⁻¹ : ℝ) else 0

/-- The removal sum with the residual function. -/
def Wtil (G : PrimeGroups) (gs : Fin G.size) (Wr : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p : Label G gs, if p.val ∣ n then ((mass G gs)⁻¹ : ℝ) * Wr (n / p.val) else 0

theorem label_dvd_le {G : PrimeGroups} {gs : Fin G.size} (p : Label G gs) {n : ℕ} (hn : 1 ≤ n)
    (hp : p.val ∣ n) : 1 ≤ p.val ∧ p.val ≤ n :=
  ⟨(label_prime p).one_lt.le, Nat.le_of_dvd (by omega) hp⟩

theorem endpoint_mul_Wtil_eq_quad (G : PrimeGroups) (gs : Fin G.size) (x : ℝ) (E : Endpoint)
    (Wr : ℕ → ℂ) (hfree : ∀ m, rough (W x) m → S56Core.GroupFree G m)
    (hαrough : ∀ m, E.alpha m ≠ 0 → rough (W x) m)
    (hinv : ∀ e k, S56Core.GroupFree G e → Wr (e * k) = Wr k)
    (N n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    endpoint G x E n * Wtil G gs Wr n =
      quad (A0 E) (S0 G gs) (P0 E x) (fun r => E.residual (groupFreePart G r) * Wr r) N n := by
  rw [quad_eq_sum_tri]
  unfold Wtil
  rw [Finset.mul_sum]
  -- both sides as sums over group primes dividing `n`
  have hL : ∀ p : Label G gs, endpoint G x E n * (if p.val ∣ n then
      ((mass G gs)⁻¹ : ℝ) * Wr (n / p.val) else 0) =
      (fun s : ℕ => if s ∣ n then S0 G gs s * tri (A0 E) (P0 E x)
        (fun r => E.residual (groupFreePart G r) * Wr r) N (n / s) else 0) p.val := by
    intro p
    simp only
    split_ifs with hp
    · have hle := label_dvd_le p hn1 hp
      have hk1 : 1 ≤ n / p.val := Nat.div_pos (Nat.le_of_dvd (by omega) hp) (by omega)
      have hkN : n / p.val ≤ N := (Nat.div_le_self _ _).trans hnN
      rw [← endpoint_mul_eq_tri G x E Wr hfree hαrough hinv N (n / p.val) hk1 hkN]
      have hend : endpoint G x E n = endpoint G x E (n / p.val) := by
        conv_lhs => rw [← Nat.mul_div_cancel' hp]
        apply endpoint_mul_supported G x E _ _ (label_prime p).ne_zero
        rw [Nat.Prime.primeFactors (label_prime p)]
        intro q hq
        rw [Finset.mem_singleton.mp hq]
        exact Finset.mem_biUnion.mpr ⟨gs, Finset.mem_univ _, p.2⟩
      rw [hend, S0, if_pos p.2]
      ring
    · rw [mul_zero]
  rw [Finset.sum_congr rfl (fun p _ => hL p)]
  rw [Finset.sum_coe_sort (G.primes gs) (fun s : ℕ => if s ∣ n then S0 G gs s * tri (A0 E) (P0 E x)
        (fun r => E.residual (groupFreePart G r) * Wr r) N (n / s) else 0)]
  rw [← Finset.sum_filter, ← Finset.sum_subset (s₁ := (G.primes gs).filter (· ∣ n))
    (s₂ := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [if_pos (Finset.mem_filter.mp hs).2]
  · intro s hs
    obtain ⟨hsP, hsn⟩ := Finset.mem_filter.mp hs
    have := label_dvd_le (⟨s, hsP⟩ : Label G gs) hn1 hsn
    exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans hnN⟩
  · intro s _ hs
    by_cases hsn : s ∣ n
    · have hsP : s ∉ G.primes gs := fun h => hs (Finset.mem_filter.mpr ⟨h, hsn⟩)
      rw [if_pos hsn, S0, if_neg hsP, zero_mul]
    · rw [if_neg hsn, mul_zero]

/-- For `n` with no square of a removed prime, the mark weight is the removal sum. -/
theorem weightedMarks_eq_Wtil {G : PrimeGroups} {t : Fin G.size → ℕ} {gs : Fin G.size}
    (ls : Fin (t gs)) (hgs : gs ∈ G.small) (q : ℝ) (hq : 0 < q)
    (b : Tuple G t → ℂ) (hb : ∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z')
    (hmass : 0 < mass G gs) (n : ℕ) (hgood : ∀ p ∈ G.primes gs, ¬ p ^ 2 ∣ n) :
    weightedMarks G q t b n = Wtil G gs (Wres G t gs ls q b) n := by
  rw [weightedMarks_eq_removal ls q b n]
  unfold Wtil
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp
  · have hpk : ¬ p.val ∣ n / p.val := by
      intro h
      apply hgood p.val p.2
      obtain ⟨c, hc⟩ := h
      exact ⟨c, by rw [pow_two, mul_assoc, ← hc, Nat.mul_div_cancel' hp]⟩
    have := removal_term_eq ls hgs q hq b hb hmass p (n / p.val) hpk
    rw [Nat.mul_div_cancel' hp] at this
    exact this
  · rfl

/-! ### Rational phases by characters -/

theorem e_int (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have : (2 * (Real.pi : ℂ) * ((k : ℝ) : ℂ) * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem e_add' (a b : ℝ) : e (a + b) = e a * e b := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem e_periodic (a : ℝ) (k : ℤ) : e (a + k) = e a := by
  rw [e_add', e_int, mul_one]

/-- The character coefficient of the rational phase. -/
def cchi (r : ℕ) (u : ℤ) (χ : DirichletCharacter ℂ r) (k : ℕ) : ℂ :=
  ((Nat.totient r : ℂ))⁻¹ * ∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
    χ ((a : ZMod r)⁻¹) * e (u * a * k / r)

theorem norm_cchi_le (r : ℕ) (u : ℤ) (χ : DirichletCharacter ℂ r) (k : ℕ) : ‖cchi r u χ k‖ ≤ 1 := by
  unfold cchi
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hcard : ((Finset.range r).filter (fun a => Nat.Coprime a r)).card = Nat.totient r := by
    rw [Nat.totient]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    rw [Nat.coprime_comm]
  rcases Nat.eq_zero_or_pos (Nat.totient r) with h0 | hpos
  · rw [h0]; simp
  · rw [inv_mul_le_iff₀ (by exact_mod_cast hpos), mul_one]
    calc ‖∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), χ ((a : ZMod r)⁻¹) *
          e (u * a * k / r)‖
        ≤ ∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ‖χ ((a : ZMod r)⁻¹) *
          e (u * a * k / r)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [norm_mul]
          have h1 := χ.norm_le_one ((a : ZMod r)⁻¹)
          have h2 : ‖e (u * a * k / r)‖ = 1 := by
            unfold e; rw [Complex.norm_exp]; simp
          rw [h2, mul_one]; exact h1
      _ = Nat.totient r := by rw [Finset.sum_const, hcard]; simp

/-- Character expansion of the rational phase on units. -/
theorem e_eq_sum_cchi (r : ℕ) (hr : 1 ≤ r) (u : ℤ) (v k : ℕ) (hv : Nat.Coprime v r) :
    e (u * (v * k : ℕ) / r) = ∑ χ : DirichletCharacter ℂ r, cchi r u χ k * χ (v : ZMod r) := by
  haveI : NeZero r := ⟨by omega⟩
  unfold cchi
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
      ∑ χ : DirichletCharacter ℂ r, ((Nat.totient r : ℂ))⁻¹ * (χ ((a : ZMod r)⁻¹) *
        e (u * a * k / r)) * χ (v : ZMod r) =
      if a = v % r then e (u * a * k / r) else 0 := by
    intro a ha
    have hau : IsUnit (a : ZMod r) :=
      (ZMod.isUnit_iff_coprime a r).mpr (Finset.mem_filter.mp ha).2
    have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hau (v : ZMod r)
    have hrw : ∀ χ : DirichletCharacter ℂ r, ((Nat.totient r : ℂ))⁻¹ * (χ ((a : ZMod r)⁻¹) *
        e (u * a * k / r)) * χ (v : ZMod r) =
        ((Nat.totient r : ℂ))⁻¹ * e (u * a * k / r) * (χ ((a : ZMod r)⁻¹) * χ (v : ZMod r)) := by
      intro χ; ring
    rw [Finset.sum_congr rfl (fun χ _ => hrw χ), ← Finset.mul_sum, horth]
    have hiff : (a : ZMod r) = (v : ZMod r) ↔ a = v % r := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (Finset.mem_range.mp
        (Finset.mem_filter.mp ha).1)]
    have htot : (Nat.totient r : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    by_cases h : a = v % r
    · rw [if_pos (hiff.mpr h), if_pos h]; field_simp
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  have hmem : v % r ∈ (Finset.range r).filter (fun a => Nat.Coprime a r) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
    show Nat.gcd (v % r) r = 1
    rw [← Nat.gcd_rec r v]
    exact hv.symm
  rw [if_pos hmem]
  -- periodicity
  have hdecomp : (u : ℝ) * ((v * k : ℕ) : ℝ) / r =
      (u : ℝ) * ((v % r : ℕ) : ℝ) * k / r + ((u * ((v / r : ℕ) : ℤ) * k : ℤ) : ℝ) := by
    have hv' : (v : ℝ) = ((v % r : ℕ) : ℝ) + r * ((v / r : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div v r).symm
    have hrpos : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [hv']
    field_simp
  rw [hdecomp, e_periodic]

theorem sum_comm4 {α ι : Type*} [AddCommMonoid α] (S : Finset ι) (A B C D : Finset ℕ)
    (F : ι → ℕ → ℕ → ℕ → ℕ → α) :
    ∑ i ∈ S, ∑ m ∈ A, ∑ s ∈ B, ∑ p ∈ C, ∑ k ∈ D, F i m s p k =
      ∑ m ∈ A, ∑ s ∈ B, ∑ p ∈ C, ∑ k ∈ D, ∑ i ∈ S, F i m s p k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]

/-- The rational phase times a four-fold convolution, expanded by characters. -/
theorem e_mul_quad (r : ℕ) (hr : 1 ≤ r) (u : ℤ) (f1 f2 f3 f4 : ℕ → ℂ) (N n : ℕ)
    (hcop : ∀ m s p, f1 m * f2 s * f3 p ≠ 0 → Nat.Coprime (m * s * p) r) :
    e (u * n / r) * quad f1 f2 f3 f4 N n =
      ∑ χ : DirichletCharacter ℂ r, quad (fun m => f1 m * χ (m : ZMod r))
        (fun s => f2 s * χ (s : ZMod r)) (fun p => f3 p * χ (p : ZMod r))
        (fun k => f4 k * cchi r u χ k) N n := by
  unfold quad
  rw [sum_comm4]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro k _
  by_cases hprod : m * s * p * k = n
  · simp only [if_pos hprod]
    by_cases hz : f1 m * f2 s * f3 p = 0
    · have : ∀ χ : DirichletCharacter ℂ r, f1 m * χ (m : ZMod r) * (f2 s * χ (s : ZMod r)) *
          (f3 p * χ (p : ZMod r)) * (f4 k * cchi r u χ k) = 0 := by
        intro χ
        have : f1 m * χ (m : ZMod r) * (f2 s * χ (s : ZMod r)) * (f3 p * χ (p : ZMod r)) *
            (f4 k * cchi r u χ k) = (f1 m * f2 s * f3 p) * (χ (m : ZMod r) * χ (s : ZMod r) *
            χ (p : ZMod r) * f4 k * cchi r u χ k) := by ring
        rw [this, hz, zero_mul]
      rw [Finset.sum_congr rfl (fun χ _ => this χ), Finset.sum_const_zero]
      have : f1 m * f2 s * f3 p * f4 k = 0 := by rw [hz, zero_mul]
      rw [this, mul_zero]
    · have hc := hcop m s p hz
      have he := e_eq_sum_cchi r hr u (m * s * p) k hc
      rw [← hprod, he, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      have hχ : χ ((m * s * p : ℕ) : ZMod r) = χ (m : ZMod r) * χ (s : ZMod r) * χ (p : ZMod r) := by
        push_cast; rw [map_mul, map_mul]
      rw [hχ]; ring
  · simp only [if_neg hprod, mul_zero, Finset.sum_const_zero]

end Erdos821.P5Marked
