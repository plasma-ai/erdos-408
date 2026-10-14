module

public import Erdos408.Extraction.TypeII.Grid
public import Erdos408.Extraction.TypeII.Endpoint

/-!
# The main term of one box

On a box `m ∈ (λ, λ(1+δ)]`, `n ∈ (μ, μ(1+δ)]` with `x/κ ≤ λμ ≤ κx`, expand the endpoint
into monomials `𝒲_S R_S`, write `R_S = 𝒩 F_S` with `F_S = clamp(R_S / 𝒩)` (exact, since
`|R_S| ≤ 𝒩` on `[1, x²]`), and apply `typeII_box` to each monomial. The distinguished bands
of a monomial satisfy the window and gap conditions by the cluster layout, and `F_S` is
invariant under their primes.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-- Restricting a real sum over `[⌈μ⌉, ⌊2μ⌋]` to `(⌊μ⌋, ⌊μ(1+δ)⌋]`. -/
theorem sum_Icc_ite_Ioc_real {mu δ : ℝ} (hmu : 0 ≤ mu) (hδ : δ ≤ 1) (f : ℕ → ℝ) :
    ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊, (if n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊ then f n else 0) =
      ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊, f n := by
  have hsub : Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊ ⊆ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊ := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
    have : mu < n := (Nat.floor_lt hmu).1 h1
    exact mem_Icc.2 ⟨Nat.ceil_le.2 this.le, h2.trans (Nat.floor_le_floor (by nlinarith))⟩
  rw [← sum_subset hsub fun n _ hn => by simp only [hn, ↓reduceIte]]
  exact sum_congr rfl fun n hn => by simp only [hn, ↓reduceIte]

/-- The data of the endpoint expansion at `x`: the cluster layout, the harmonic masses, small
band primes, and the bound `𝒩` for the remainders on `[1, x²]`. -/
structure EndpointData (q cw : ℝ) (K : ℕ) (CN x : ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ)
    (B : (Fin k → ℕ) → ℝ) (𝒩 : ℝ) : Prop where
  one_le_K : 1 ≤ K
  q_pos : 0 < q
  log_gt : 1 < Real.log x
  logLog_pos : 0 < logLog x
  layout : 2 * ((inertPerCluster K CN x : ℝ) + 1) * K ≤ 4 / 100 * logLog x
  small : ∀ a : ℝ, a ≤ 19 / 100 → ∀ p ∈ band x a, ∀ i, (p : ℝ) ≤ x ^ u i
  norm_pos : 0 < 𝒩
  rest_le : ∀ S ∈ clusterSets K (inertPerCluster K CN x), ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 →
    |monoRest q cw K x u v B S h| ≤ 𝒩

/-- The main term of one box: `|∑_box P (f - C) α β| ≤ |𝒮| 𝒩 C₂ λμ L^{-12}`. -/
theorem abs_box_main_le {q cw : ℝ} {K : ℕ} {CN c Ch Cj κ C₂ x 𝒩 : ℝ} {k : ℕ}
    {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B 𝒩) (hbox : BoxBound q K c Ch Cj κ C₂ x)
    {lam mu δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlam : x ^ presieveExponent c Ch x ≤ lam) (hmu : x ^ presieveExponent c Ch x ≤ mu)
    (hxγ : 1 ≤ x ^ presieveExponent c Ch x) (h1 : x / κ ≤ lam * mu) (h2 : lam * mu ≤ κ * x)
    (hsq : 4 * (lam * mu) ≤ x ^ 2) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : (j : ℝ) ≤ Cj * logLogLog x + 1) (βc : ℕ → ℝ)
    (hβc : ∀ n, βc n ≠ 0 → (∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) ∧
      0 ≤ βc n ∧ βc n ≤ Real.log x ^ (3 : ℝ)) :
    |∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
        endpoint q cw K CN x u v B (m * n - 1) * primeProxyDiff x (presieveExponent c Ch x) j m *
          βc n| ≤
      (clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
        (C₂ * (lam * mu) * Real.log x ^ (-12 : ℝ)) := by
  set γ := presieveExponent c Ch x
  set N' := inertPerCluster K CN x
  set 𝒮 := clusterSets K N'
  have hlam0 : 1 ≤ lam := hxγ.trans hlam
  have hmu0 : 1 ≤ mu := hxγ.trans hmu
  -- the companion restricted to the `n`-cell
  set βb : ℕ → ℝ := fun n => if n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊ then βc n else 0 with hβb
  have hn_range : ∀ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∀ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
      1 ≤ m * n - 1 ∧ ((m * n - 1 : ℕ) : ℝ) ≤ x ^ 2 := by
    intro m hm n hn
    obtain ⟨hm1, hm2⟩ := mem_Ioc.1 hm
    obtain ⟨hn1, hn2⟩ := mem_Icc.1 hn
    have hlm : lam < m := (Nat.floor_lt (by linarith)).1 hm1
    have hm2' : (m : ℝ) ≤ lam * (1 + δ) := (Nat.le_floor_iff' (by
      have : (0 : ℝ) < m := by linarith
      exact_mod_cast this.ne')).1 hm2
    have hmun : mu ≤ n := Nat.ceil_le.1 hn1
    have hn2' : (n : ℝ) ≤ 2 * mu := (Nat.le_floor_iff (by linarith)).1 hn2
    have hm2 : 2 ≤ m := by
      have : (1 : ℝ) < m := by linarith
      exact_mod_cast this
    have hn1' : 1 ≤ n := by
      have : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hm2n' : 2 ≤ m * n := le_trans hm2 (Nat.le_mul_of_pos_right m hn1')
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub (by omega)]
    push_cast
    have hmn : (m : ℝ) * n ≤ lam * (1 + δ) * (2 * mu) :=
      mul_le_mul hm2' hn2' (by linarith) (by nlinarith)
    have h4 : lam * (1 + δ) * (2 * mu) ≤ 4 * (lam * mu) := by
      have : lam * (1 + δ) * (2 * mu) = 2 * (1 + δ) * (lam * mu) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by nlinarith)
    linarith
  -- each monomial is bounded by the box estimate
  have hmono : ∀ S ∈ 𝒮, |∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
      primeProxyDiff x γ j m * βb n * clampOne (monoRest q cw K x u v B S (m * n - 1) / 𝒩) *
        markedWeight Finset.univ q (fun i => band x (distExponent K x S i)) (m * n - 1)| ≤
      C₂ * (lam * mu) * Real.log x ^ (-12 : ℝ) := by
    intro S hS
    have hd : ∀ c, distIndex S c < N' := fun c =>
      mem_range.1 (((mem_clusterSets.1 hS) c).2 (distIndex_mem ((mem_clusterSets.1 hS) c).1))
    have hwin : ∀ i, 11 / 100 ≤ distExponent K x S i ∧ distExponent K x S i ≤ 19 / 100 :=
      fun i => inertExponent_mem hE.one_le_K hE.logLog_pos hE.layout i.isLt (hd i)
    have hgap : ∀ i i' : Fin K, i < i' →
        distExponent K x S i + 4 / 100 / K ≤ distExponent K x S i' := fun i i' h =>
      distExponent_gap hE.one_le_K hE.logLog_pos hE.layout hS h
    have hdisj := layout_disjoint (N' := N') hE.one_le_K hE.log_gt hE.logLog_pos hE.layout
    have hF : ∀ h, ‖((clampOne (monoRest q cw K x u v B S h / 𝒩) : ℝ) : ℂ)‖ ≤ 1 := fun h => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_clampOne_le _
    have hFinv : ∀ i h, ∀ p ∈ band x (distExponent K x S i),
        ((clampOne (monoRest q cw K x u v B S (p * h) / 𝒩) : ℝ) : ℂ) =
          ((clampOne (monoRest q cw K x u v B S h / 𝒩) : ℝ) : ℂ) := by
      intro i h p hp
      rw [monoRest_prime_mul u v B hS hdisj i hp (hE.small _ (hwin i).2 p hp) h]
    have hβ : ∀ n, (βb n : ℂ) ≠ 0 → mu < n ∧ (n : ℝ) ≤ 2 * mu ∧
        (∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) ∧
        ‖(βb n : ℂ)‖ ≤ Real.log x ^ (3 : ℝ) := by
      intro n hn
      have hnI : n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊ := by
        by_contra h
        exact hn (by simp only [hβb, h, ↓reduceIte, Complex.ofReal_zero])
      have hβn : βb n = βc n := by simp only [hβb, hnI, ↓reduceIte]
      rw [hβn] at hn ⊢
      have hne : βc n ≠ 0 := fun h => hn (by rw [h, Complex.ofReal_zero])
      obtain ⟨hpf, h0, h3⟩ := hβc n hne
      obtain ⟨hn1, hn2⟩ := mem_Ioc.1 hnI
      have hn2' : (n : ℝ) ≤ mu * (1 + δ) := (Nat.le_floor_iff' (by omega)).1 hn2
      refine ⟨(Nat.floor_lt (by linarith)).1 hn1, by nlinarith, hpf, ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      exact h3
    have hb := hbox (distExponent K x S) (fun h => (clampOne (monoRest q cw K x u v B S h / 𝒩) : ℂ))
      lam mu lam (lam * (1 + δ)) j (fun n => (βb n : ℂ)) hwin hgap hF hFinv hlam hmu h1 h2
      le_rfl (by nlinarith) hj1 hj2 hβ
    calc _ = ‖((∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
            primeProxyDiff x γ j m * βb n *
              clampOne (monoRest q cw K x u v B S (m * n - 1) / 𝒩) *
              markedWeight Finset.univ q (fun i => band x (distExponent K x S i)) (m * n - 1) :
                ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by
          push_cast
          exact hb
  -- expand the endpoint and sum over the monomials
  have hexp : ∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
        endpoint q cw K CN x u v B (m * n - 1) * primeProxyDiff x γ j m * βc n =
      ∑ S ∈ 𝒮, 𝒩 * ∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
        primeProxyDiff x γ j m * βb n * clampOne (monoRest q cw K x u v B S (m * n - 1) / 𝒩) *
          markedWeight Finset.univ q (fun i => band x (distExponent K x S i)) (m * n - 1) := by
    have hrow : ∀ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊,
        ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
          endpoint q cw K CN x u v B (m * n - 1) * primeProxyDiff x γ j m * βc n =
        ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
          endpoint q cw K CN x u v B (m * n - 1) * primeProxyDiff x γ j m * βb n := by
      intro m _
      rw [← sum_Icc_ite_Ioc_real (by linarith) hδ1]
      refine sum_congr rfl fun n _ => ?_
      simp only [hβb]
      split_ifs <;> simp
    rw [sum_congr rfl hrow]
    have hpt : ∀ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∀ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
        endpoint q cw K CN x u v B (m * n - 1) * primeProxyDiff x γ j m * βb n =
          ∑ S ∈ 𝒮, 𝒩 * (primeProxyDiff x γ j m * βb n *
            clampOne (monoRest q cw K x u v B S (m * n - 1) / 𝒩) *
            markedWeight Finset.univ q (fun i => band x (distExponent K x S i)) (m * n - 1)) := by
      intro m hm n hn
      obtain ⟨hh1, hh2⟩ := hn_range m hm n hn
      rw [endpoint_eq_sum q cw hE.q_pos.ne' K CN x u v B, sum_mul, sum_mul]
      refine sum_congr rfl fun S hS => ?_
      have hR := hE.rest_le S hS _ hh1 hh2
      have hcl : 𝒩 * clampOne (monoRest q cw K x u v B S (m * n - 1) / 𝒩) =
          monoRest q cw K x u v B S (m * n - 1) := by
        rw [clampOne_of_abs_le (by rw [abs_div, abs_of_pos hE.norm_pos]; exact
          (div_le_one hE.norm_pos).2 hR)]
        field_simp [hE.norm_pos.ne']
      generalize clampOne (monoRest q cw K x u v B S (m * n - 1) / 𝒩) = C at hcl ⊢
      rw [← hcl]
      unfold distExponent
      ring
    rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hpt m hm n hn]
    simp only [mul_sum]
    rw [sum_congr rfl fun m _ => sum_comm, sum_comm]
  rw [hexp]
  calc |∑ S ∈ 𝒮, 𝒩 * _| ≤ ∑ S ∈ 𝒮, |𝒩 * _| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ 𝒮, 𝒩 * (C₂ * (lam * mu) * Real.log x ^ (-12 : ℝ)) := by
        refine sum_le_sum fun S hS => ?_
        rw [abs_mul, abs_of_pos hE.norm_pos]
        exact mul_le_mul_of_nonneg_left (hmono S hS) hE.norm_pos.le
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end Erdos408.TypeII
