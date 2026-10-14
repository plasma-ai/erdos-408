import Mathlib
import Erdos821.Prelim.SieveCalculus
import Erdos821.Prelim.BlockSieve
import Erdos821.Prelim.SieveGeometry
import Erdos821.Blueprint.Sieve

/-!
# Sieve level: support products are `≤ z^{4h+2}` (`lem:sieve`)

For `z > 1`, blocks `B_j = Block S z j` (`Z_{j+1} < p ≤ Z_j` with
`Z_j = z^{1/2^j}`), caps `e_j = (j+1)*h`, and `J = range N`, every
`d ∈ SieveSupport (J.biUnion B) J B e` satisfies
`(∏ p ∈ d, (p:ℝ)) ≤ z^{4h+2}`. Per-block `∏_{d∩B_j} ≤ Z_j^{e_j}`
(`Block_le_Z` + `Zscale ≥ 1`), product over `j` via disjoint
decomposition (as in `sieve_prod_le`), then
`∏ Z_j^{e_j} = z^{∑ e_j/2^j} ≤ z^{4h}` via `rpow` + `level_sum_le`,
and `z^{4h} ≤ z^{4h+2}`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- `Z_j^{e} = z^{(e:ℝ)/2^j}` via `rpow`. -/
theorem Zscale_pow_eq (z : ℝ) (hz : 0 ≤ z) (j e : ℕ) :
    (Zscale z j) ^ e = z ^ (((e : ℕ) : ℝ) / (2 : ℝ) ^ j) := by
  unfold Zscale
  have h1 : ((z ^ ((1 : ℝ) / (2 : ℝ) ^ j)) ^ e : ℝ)
      = z ^ (((1 : ℝ) / (2 : ℝ) ^ j) * ((e : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast _ e, ← Real.rpow_mul hz]
  rw [h1]
  congr 1
  ring

/-- Product of `z`-rpow factors is `z` to the sum. -/
theorem rpow_prod_eq (z : ℝ) (hz : 0 < z) (J : Finset ℕ) (a : ℕ → ℝ) :
    ∏ j ∈ J, z ^ (a j) = z ^ (∑ j ∈ J, a j) := by
  induction J using Finset.induction with
  | empty => simp [Real.rpow_zero]
  | @insert k s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has, ih,
      ← Real.rpow_add hz]

/-- Upper support level bound (real product). -/
theorem support_level_le (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (h N : ℕ) (d : Finset ℕ)
    (hd : d ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range N).biUnion (fun j => Block α S z j))
      (Finset.range N) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    ∏ p ∈ d, (p : ℝ) ≤ z ^ (4 * h + 2 : ℕ) := by
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
  have hz1le : (1 : ℝ) ≤ z := le_of_lt hz
  -- unpack support
  have hdm := (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hd
  obtain ⟨hdP, hcon⟩ := hdm
  have hdisj : ∀ j₁ ∈ Finset.range N, ∀ j₂ ∈ Finset.range N, j₁ ≠ j₂ →
      Disjoint (Block α S z j₁) (Block α S z j₂) := by
    intro j₁ _ j₂ _ hne
    exact Block_disjoint α S z hz hne
  -- decomposition `d = J.biUnion (d ∩ B ·)`
  have hdecomp : (Finset.range N).biUnion (fun j => d ∩ Block α S z j) = d := by
    apply le_antisymm
    · intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨j, _, hj⟩ := hp
      exact (Finset.mem_inter.mp hj).1
    · intro p hp
      have hpp := hdP hp
      rw [Finset.mem_biUnion] at hpp ⊢
      obtain ⟨j, hjJ, hjB⟩ := hpp
      exact ⟨j, hjJ, Finset.mem_inter.mpr ⟨hp, hjB⟩⟩
  have hPD : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun j => d ∩ Block α S z j) := by
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    simp only [Function.onFun]
    exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
      (hdisj j₁ hj₁ j₂ hj₂ hne)
  -- per-block real bound `∏_{d∩B_j} ≤ Z_j^{e_j}`
  have hinner : ∀ j ∈ Finset.range N,
      ∏ p ∈ d ∩ Block α S z j, (p : ℝ) ≤ (Zscale z j) ^ ((j + 1) * h) := by
    intro j hj
    have hZ1 : (1 : ℝ) ≤ Zscale z j := le_of_lt (Zscale_gt_one hz j)
    have hcard : (d ∩ Block α S z j).card ≤ (j + 1) * h := hcon j hj
    calc ∏ p ∈ d ∩ Block α S z j, (p : ℝ)
        ≤ ∏ _p ∈ d ∩ Block α S z j, Zscale z j := by
          apply Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _)
          intro p hp
          exact Block_le_Z α S z j p (Finset.mem_inter.mp hp).2
      _ = (Zscale z j) ^ ((d ∩ Block α S z j).card) := Finset.prod_const _
      _ ≤ (Zscale z j) ^ ((j + 1) * h) :=
          pow_le_pow_right₀ hZ1 hcard
  -- assemble `∏_d = ∏_j ∏_{d∩B_j} ≤ ∏_j Z_j^{e_j}`
  have hprod_eq : ∏ p ∈ d, (p : ℝ)
      = ∏ j ∈ Finset.range N, ∏ p ∈ d ∩ Block α S z j, (p : ℝ) := by
    conv_lhs => rw [← hdecomp]
    rw [Finset.prod_biUnion hPD]
  have hprod_le : ∏ p ∈ d, (p : ℝ)
      ≤ ∏ j ∈ Finset.range N, (Zscale z j) ^ ((j + 1) * h) := by
    rw [hprod_eq]
    apply Finset.prod_le_prod₀
    · intro j hj
      apply Finset.prod_nonneg
      intro p _
      exact Nat.cast_nonneg _
    · intro j hj
      exact hinner j hj
  -- rewrite each `Z_j^{e_j}` as `z`-rpow
  have hZeq : ∀ j ∈ Finset.range N,
      (Zscale z j) ^ ((j + 1) * h)
        = z ^ ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j) :=
    fun j _ => Zscale_pow_eq z hz0.le j ((j + 1) * h)
  have hprod_rpow : ∏ j ∈ Finset.range N, (Zscale z j) ^ ((j + 1) * h)
      = z ^ (∑ j ∈ Finset.range N, ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j)) := by
    have : ∏ j ∈ Finset.range N, (Zscale z j) ^ ((j + 1) * h)
        = ∏ j ∈ Finset.range N, z ^ ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hZeq j hj
    rw [this]
    exact rpow_prod_eq z hz0 _ _
  -- exponent sum `≤ 4h`
  have hexp_le : ∑ j ∈ Finset.range N,
      ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j) ≤ ((4 * h : ℕ) : ℝ) := by
    have hsum : ∑ j ∈ Finset.range N,
        ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j)
        = (h : ℝ) * ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hsum]
    have h4 : ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j) ≤ 4 :=
      Prelim.SieveCalculus.level_sum_le N
    calc (h : ℝ) * ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j)
        ≤ (h : ℝ) * 4 := by
          apply mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
      _ = (((4 * h : ℕ) : ℝ)) := by push_cast; ring
  have hmain : ∏ j ∈ Finset.range N, (Zscale z j) ^ ((j + 1) * h)
      ≤ z ^ (((4 * h : ℕ) : ℝ)) := by
    rw [hprod_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hz1le hexp_le
  have hnat_eq : z ^ (((4 * h : ℕ) : ℝ)) = z ^ (4 * h : ℕ) := by
    rw [Real.rpow_natCast]
  have hle4 : z ^ (4 * h : ℕ) ≤ z ^ (4 * h + 2 : ℕ) := by
    apply pow_le_pow_right₀ hz1le
    omega
  calc ∏ p ∈ d, (p : ℝ) ≤ ∏ j ∈ Finset.range N, (Zscale z j) ^ ((j + 1) * h) :=
        hprod_le
    _ ≤ z ^ (((4 * h : ℕ) : ℝ)) := hmain
    _ = z ^ (4 * h : ℕ) := hnat_eq
    _ ≤ z ^ (4 * h + 2 : ℕ) := hle4

/-- Correction support level: one block has `e+1` instead of `≤e`;
still `≤ z^{4h+2}` since the extra `1/2^{j₀} ≤ 1`. -/
theorem corr_level_le (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (h N j₀ : ℕ) (hj₀ : j₀ ∈ Finset.range N)
    (d : Finset ℕ)
    (hdP : d ⊆ (Finset.range N).biUnion (fun j => Block α S z j))
    (hcon_le : ∀ j ∈ Finset.range N, j ≠ j₀ → (d ∩ Block α S z j).card ≤ (j + 1) * h)
    (hcon_eq : (d ∩ Block α S z j₀).card = (j₀ + 1) * h + 1) :
    ∏ p ∈ d, (p : ℝ) ≤ z ^ (4 * h + 2 : ℕ) := by
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
  have hz1le : (1 : ℝ) ≤ z := le_of_lt hz
  have hdisj : ∀ j₁ ∈ Finset.range N, ∀ j₂ ∈ Finset.range N, j₁ ≠ j₂ →
      Disjoint (Block α S z j₁) (Block α S z j₂) := by
    intro j₁ _ j₂ _ hne
    exact Block_disjoint α S z hz hne
  have hdecomp : (Finset.range N).biUnion (fun j => d ∩ Block α S z j) = d := by
    apply le_antisymm
    · intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨j, _, hj⟩ := hp
      exact (Finset.mem_inter.mp hj).1
    · intro p hp
      have hpp := hdP hp
      rw [Finset.mem_biUnion] at hpp ⊢
      obtain ⟨j, hjJ, hjB⟩ := hpp
      exact ⟨j, hjJ, Finset.mem_inter.mpr ⟨hp, hjB⟩⟩
  have hPD : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun j => d ∩ Block α S z j) := by
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    simp only [Function.onFun]
    exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
      (hdisj j₁ hj₁ j₂ hj₂ hne)
  -- caps with one extra in `j₀`
  have hcap : ∀ j ∈ Finset.range N,
      (d ∩ Block α S z j).card ≤ (j + 1) * h + (if j = j₀ then 1 else 0) := by
    intro j hj
    by_cases heq : j = j₀
    · subst heq
      rw [if_pos rfl, hcon_eq]
    · rw [if_neg heq]
      exact hcon_le j hj heq
  have hinner : ∀ j ∈ Finset.range N,
      ∏ p ∈ d ∩ Block α S z j, (p : ℝ)
        ≤ (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0)) := by
    intro j hj
    have hZ1 : (1 : ℝ) ≤ Zscale z j := le_of_lt (Zscale_gt_one hz j)
    have hcard := hcap j hj
    calc ∏ p ∈ d ∩ Block α S z j, (p : ℝ)
        ≤ ∏ _p ∈ d ∩ Block α S z j, Zscale z j := by
          apply Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _)
          intro p hp
          exact Block_le_Z α S z j p (Finset.mem_inter.mp hp).2
      _ = (Zscale z j) ^ ((d ∩ Block α S z j).card) := Finset.prod_const _
      _ ≤ (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0)) :=
          pow_le_pow_right₀ hZ1 hcard
  have hprod_eq : ∏ p ∈ d, (p : ℝ)
      = ∏ j ∈ Finset.range N, ∏ p ∈ d ∩ Block α S z j, (p : ℝ) := by
    conv_lhs => rw [← hdecomp]
    rw [Finset.prod_biUnion hPD]
  have hprod_le : ∏ p ∈ d, (p : ℝ)
      ≤ ∏ j ∈ Finset.range N,
        (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0)) := by
    rw [hprod_eq]
    apply Finset.prod_le_prod₀
    · intro j hj
      apply Finset.prod_nonneg
      intro p _
      exact Nat.cast_nonneg _
    · intro j hj
      exact hinner j hj
  have hZeq : ∀ j ∈ Finset.range N,
      (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0))
        = z ^ (((((j + 1) * h + (if j = j₀ then 1 else 0) : ℕ)) : ℝ)
          / (2 : ℝ) ^ j) :=
    fun j _ => Zscale_pow_eq z hz0.le j _
  have hprod_rpow : ∏ j ∈ Finset.range N,
      (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0))
      = z ^ (∑ j ∈ Finset.range N,
        (((((j + 1) * h + (if j = j₀ then 1 else 0) : ℕ)) : ℝ)
          / (2 : ℝ) ^ j)) := by
    have : ∏ j ∈ Finset.range N,
        (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0))
        = ∏ j ∈ Finset.range N, z ^
          (((((j + 1) * h + (if j = j₀ then 1 else 0) : ℕ)) : ℝ)
            / (2 : ℝ) ^ j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hZeq j hj
    rw [this]
    exact rpow_prod_eq z hz0 _ _
  -- exponent `≤ 4h+1`
  have hexp_le : ∑ j ∈ Finset.range N,
      (((((j + 1) * h + (if j = j₀ then 1 else 0) : ℕ)) : ℝ) / (2 : ℝ) ^ j)
      ≤ (((4 * h + 1 : ℕ)) : ℝ) := by
    have hsplit : ∀ j ∈ Finset.range N,
        (((((j + 1) * h + (if j = j₀ then 1 else 0) : ℕ)) : ℝ) / (2 : ℝ) ^ j)
        = ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j)
          + ((if j = j₀ then (1 : ℝ) else 0) / (2 : ℝ) ^ j) := by
      intro j _
      by_cases heq : j = j₀
      · subst heq
        simp only [if_pos rfl]
        push_cast
        ring
      · simp only [if_neg heq]
        push_cast
        ring
    have hsum_eq : ∑ j ∈ Finset.range N,
        (((((j + 1) * h + (if j = j₀ then 1 else 0) : ℕ)) : ℝ) / (2 : ℝ) ^ j)
        = (∑ j ∈ Finset.range N, ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j))
          + (∑ j ∈ Finset.range N, ((if j = j₀ then (1 : ℝ) else 0) / (2 : ℝ) ^ j)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact hsplit j hj
    rw [hsum_eq]
    have hbase : ∑ j ∈ Finset.range N, ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j)
        ≤ ((4 * h : ℕ) : ℝ) := by
      have hsum : ∑ j ∈ Finset.range N,
          ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j)
          = (h : ℝ) * ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        ring
      rw [hsum]
      have h4 : ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j) ≤ 4 :=
        Prelim.SieveCalculus.level_sum_le N
      calc (h : ℝ) * ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (2 : ℝ) ^ j)
          ≤ (h : ℝ) * 4 := by
            apply mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
        _ = (((4 * h : ℕ) : ℝ)) := by push_cast; ring
    have hextra : ∑ j ∈ Finset.range N,
        ((if j = j₀ then (1 : ℝ) else 0) / (2 : ℝ) ^ j) ≤ 1 := by
      have hsingle : ∑ j ∈ Finset.range N,
          ((if j = j₀ then (1 : ℝ) else 0) / (2 : ℝ) ^ j)
          = (1 : ℝ) / (2 : ℝ) ^ j₀ := by
        rw [Finset.sum_eq_single j₀]
        · simp
        · intro j _ hjne
          simp [hjne]
        · intro hcon
          exact absurd hj₀ hcon
      rw [hsingle]
      have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ j₀ :=
        one_le_pow₀ (by norm_num)
      have hpos : (0 : ℝ) < (2 : ℝ) ^ j₀ := pow_pos (by norm_num) _
      rw [div_le_one hpos]
      exact hpow1
    calc (∑ j ∈ Finset.range N, ((((j + 1) * h : ℕ) : ℝ) / (2 : ℝ) ^ j))
          + (∑ j ∈ Finset.range N, ((if j = j₀ then (1 : ℝ) else 0) / (2 : ℝ) ^ j))
        ≤ ((4 * h : ℕ) : ℝ) + 1 := add_le_add hbase hextra
      _ = ((((4 * h + 1 : ℕ)) : ℝ)) := by push_cast; ring
  have hmain : ∏ j ∈ Finset.range N,
      (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0))
      ≤ z ^ ((((4 * h + 1 : ℕ)) : ℝ)) := by
    rw [hprod_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hz1le hexp_le
  have hnat_eq : z ^ ((((4 * h + 1 : ℕ)) : ℝ)) = z ^ (4 * h + 1 : ℕ) := by
    rw [Real.rpow_natCast]
  have hle : z ^ (4 * h + 1 : ℕ) ≤ z ^ (4 * h + 2 : ℕ) := by
    apply pow_le_pow_right₀ hz1le
    omega
  calc ∏ p ∈ d, (p : ℝ)
      ≤ ∏ j ∈ Finset.range N,
        (Zscale z j) ^ ((j + 1) * h + (if j = j₀ then 1 else 0)) := hprod_le
    _ ≤ z ^ ((((4 * h + 1 : ℕ)) : ℝ)) := hmain
    _ = z ^ (4 * h + 1 : ℕ) := hnat_eq
    _ ≤ z ^ (4 * h + 2 : ℕ) := hle

end PrelimLemmas
end Erdos821
