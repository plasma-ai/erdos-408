import Erdos821.P5MarkedEnergy.BoxJ3
import Erdos821.P5MarkedEnergy.SmoothPartition
import Erdos821.P5MarkedEnergy.ErrorBound
import Erdos821.P5.MarkedEnergyTask

/-! The coefficientwise decomposition of the marked endpoint energy coefficient
into smooth pieces and characters, plus the square-multiple error. -/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- A smooth piece of the expanded coefficient. -/
def bpiece (G : PrimeGroups) (x Y v lo : ℝ) (E : Endpoint) (Ψ : ℝ → ℂ) (gs : Fin G.size)
    (Wr : ℕ → ℂ) (r : ℕ) (u : ℤ) (N : ℕ) (i : ℕ) (χ : DirichletCharacter ℂ r) (n : ℕ) : ℂ :=
  (Ψ (n / Y) * (psi lo i (n / Y) : ℂ)) * mellin n v *
    quad (cf1 E r χ) (cf2 G gs r χ) (cf3 E x r χ) (cf4 G E Wr r u χ) N n

/-- The square-multiple error. -/
def epsf (P : Geometry) (G : PrimeGroups) (x Y v : ℝ) (E : Endpoint) (t : Fin G.size → ℕ)
    (b : Tuple G t → ℂ) (Ψ : ℝ → ℂ) (gs : Fin G.size) (Wr : ℕ → ℂ) (r : ℕ) (u : ℤ) (n : ℕ) : ℂ :=
  Ψ (n / Y) * mellin n v * e (u * n / r) * endpoint G x E n *
    (weightedMarks G P.q t b n - Wtil G gs Wr n)

theorem pointwise_decomposition (P : Geometry) (G : PrimeGroups) (x Y v lo hi : ℝ) (E : Endpoint)
    (t : Fin G.size → ℕ) (b : Tuple G t → ℂ) (Ψ : ℝ → ℂ) (gs : Fin G.size) (Wr : ℕ → ℂ)
    (r : ℕ) (u : ℤ) (kk : ℕ) (hr : 1 ≤ r) (hlo : 0 < lo) (hY : 0 < Y)
    (hkk : hi ≤ ptA lo kk) (hsupp : Function.support Ψ ⊆ Set.Icc lo hi)
    (hfree : ∀ m, rough (W x) m → S56Core.GroupFree G m)
    (hαrough : ∀ m, E.alpha m ≠ 0 → rough (W x) m)
    (hinv : ∀ e k, S56Core.GroupFree G e → Wr (e * k) = Wr k)
    (hcop : ∀ m s p, A0 E m * S0 G gs s * P0 E x p ≠ 0 → Nat.Coprime (m * s * p) r)
    (n : ℕ) (hn : n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊) :
    P5Core.markedEnergyCoefficient P G x Y v E t b Ψ n * e ((u : ℝ) / r * n) =
      ∑ p : Fin kk × DirichletCharacter ℂ r,
          bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ p.1 p.2 n +
        epsf P G x Y v E t b Ψ gs Wr r u n := by
  set N := ⌊hi * Y⌋₊ with hN
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  have hnpos : 1 ≤ n := by
    have : (0 : ℝ) < lo * Y := by positivity
    have : 0 < ⌈lo * Y⌉₊ := Nat.ceil_pos.mpr this
    omega
  have he : e ((u : ℝ) / r * n) = e (u * n / r) := by congr 1; ring
  have hquad := endpoint_mul_Wtil_eq_quad G gs x E Wr hfree hαrough hinv N n hnpos hn2
  have hchar := e_mul_quad r hr u (A0 E) (S0 G gs) (P0 E x)
    (fun k => E.residual (groupFreePart G k) * Wr k) N n hcop
  -- the partition of unity
  have hpsi : Ψ (n / Y) = ∑ i ∈ Finset.range kk, Ψ (n / Y) * (psi lo i (n / Y) : ℂ) := by
    by_cases hΨ : Ψ (n / Y) = 0
    · simp [hΨ]
    · have hmem := hsupp hΨ
      rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_psi_eq_one hlo kk hkk hmem]
      simp
  unfold P5Core.markedEnergyCoefficient epsf
  rw [he]
  have hsplit : Ψ (n / Y) * mellin n v * endpoint G x E n * weightedMarks G P.q t b n *
      e (u * n / r) = Ψ (n / Y) * mellin n v * (e (u * n / r) * (endpoint G x E n *
        Wtil G gs Wr n)) + Ψ (n / Y) * mellin n v * e (u * n / r) * endpoint G x E n *
        (weightedMarks G P.q t b n - Wtil G gs Wr n) := by ring
  rw [hsplit]
  congr 1
  rw [hquad, hchar, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  simp only [bpiece]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    Fin.sum_univ_eq_sum_range (fun i => Ψ (n / Y) * (psi lo i (n / Y) : ℂ)) kk, ← hpsi]
  rfl

theorem epsf_eq_zero_of_good (P : Geometry) (G : PrimeGroups) (x Y v : ℝ) (E : Endpoint)
    (t : Fin G.size → ℕ) (b : Tuple G t → ℂ) (Ψ : ℝ → ℂ) (gs : Fin G.size) (ls : Fin (t gs))
    (r : ℕ) (u : ℤ) (hgs : gs ∈ G.small)
    (hb : ∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z')
    (hmass : 0 < mass G gs) (n : ℕ) (hgood : ∀ p ∈ G.primes gs, ¬ p ^ 2 ∣ n) :
    epsf P G x Y v E t b Ψ gs (Wres G t gs ls P.q b) r u n = 0 := by
  unfold epsf
  rw [weightedMarks_eq_Wtil ls hgs P.q P.damping.1 b hb hmass n hgood, sub_self, mul_zero]

theorem norm_Wtil_le (G : PrimeGroups) (gs : Fin G.size) (Wr : ℕ → ℂ) (Wb : ℝ)
    (hWb : ∀ k, ‖Wr k‖ ≤ Wb) (hmass : 0 < mass G gs) (n : ℕ) :
    ‖Wtil G gs Wr n‖ ≤ ((G.primes gs).filter (fun p => p ∣ n)).card * ((mass G gs)⁻¹ * Wb) := by
  unfold Wtil
  have hWb0 : 0 ≤ Wb := (norm_nonneg _).trans (hWb 0)
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p : Label G gs, ‖if p.val ∣ n then ((mass G gs)⁻¹ : ℝ) * Wr (n / p.val) else 0‖ ≤
      if p.val ∣ n then (mass G gs)⁻¹ * Wb else 0 := by
    intro p
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
      exact mul_le_mul_of_nonneg_left (hWb _) (inv_nonneg.mpr hmass.le)
    · simp
  refine (Finset.sum_le_sum fun p _ => hterm p).trans (le_of_eq ?_)
  rw [Finset.sum_coe_sort (G.primes gs) (fun p => if p ∣ n then (mass G gs)⁻¹ * Wb else 0),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem norm_quad_le (f1 f2 f3 f4 : ℕ → ℂ) (B1 B2 B3 B4 : ℝ) (h1 : ∀ m, ‖f1 m‖ ≤ B1)
    (h2 : ∀ m, ‖f2 m‖ ≤ B2) (h3 : ∀ m, ‖f3 m‖ ≤ B3) (h4 : ∀ m, ‖f4 m‖ ≤ B4) (N n : ℕ)
    (hn : 1 ≤ n) :
    ‖quad f1 f2 f3 f4 N n‖ ≤ (n.divisors.card : ℝ) ^ 3 * (B1 * B2 * B3 * B4) := by
  rw [quad_eq_sum_icc4, ← Finset.sum_filter]
  have hB : ∀ z : Q4, ‖f1 z.1 * f2 z.2.1 * f3 z.2.2.1 * f4 z.2.2.2‖ ≤ B1 * B2 * B3 * B4 := by
    intro z
    rw [norm_mul, norm_mul, norm_mul]
    have b1 : 0 ≤ B1 := (norm_nonneg _).trans (h1 0)
    have b2 : 0 ≤ B2 := (norm_nonneg _).trans (h2 0)
    have b3 : 0 ≤ B3 := (norm_nonneg _).trans (h3 0)
    gcongr
    · exact h1 _
    · exact h2 _
    · exact h3 _
    · exact h4 _
  have hB0 : 0 ≤ B1 * B2 * B3 * B4 := (norm_nonneg _).trans (hB (0, 0, 0, 0))
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun z _ => hB z).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hB0
  have hcard : ((icc4 N).filter (fun z => prod4 z = n)).card ≤ n.divisors.card ^ 3 := by
    have hinj : Set.InjOn (fun z : Q4 => (z.1, z.2.1, z.2.2.1))
        ((icc4 N).filter (fun z => prod4 z = n) : Set Q4) := by
      intro z hz z' hz' heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, icc4, Finset.mem_product,
        Finset.mem_Icc] at hz hz'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨e1, e2, e3⟩ := heq
      have hp := hz.2; have hp' := hz'.2
      unfold prod4 at hp hp'
      have hpos : 0 < z.1 * z.2.1 * z.2.2.1 := by
        have := hz.1.1.1; have := hz.1.2.1.1; have := hz.1.2.2.1.1; positivity
      have e4 : z.2.2.2 = z'.2.2.2 := by
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [← e1, ← e2, ← e3] at hp'
        rw [hp, hp']
      exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
    have hmaps : ∀ z ∈ (icc4 N).filter (fun z => prod4 z = n),
        (z.1, z.2.1, z.2.2.1) ∈ n.divisors ×ˢ n.divisors ×ˢ n.divisors := by
      intro z hz
      simp only [Finset.mem_filter] at hz
      have hp := hz.2
      unfold prod4 at hp
      simp only [Finset.mem_product, Nat.mem_divisors]
      refine ⟨⟨⟨z.2.1 * z.2.2.1 * z.2.2.2, by rw [← hp]; ring⟩, by omega⟩,
        ⟨⟨z.1 * z.2.2.1 * z.2.2.2, by rw [← hp]; ring⟩, by omega⟩,
        ⟨⟨z.1 * z.2.1 * z.2.2.2, by rw [← hp]; ring⟩, by omega⟩⟩
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [Finset.card_product, pow_succ, mul_assoc] using this
  exact_mod_cast hcard

end Erdos821.P5Marked
