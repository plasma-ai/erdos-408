import Mathlib
import Erdos821.Prelim.BlockSieve
import Erdos821.Prelim.SieveGeometry
import Erdos821.Prelim.SieveExpectation
import Erdos821.Prelim.SieveCounting
import Erdos821.Prelim.SieveLevel
import Erdos821.Prelim.SieveErrors
import Erdos821.Blueprint.Sieve

/-!
# Sieve counting, lower part (`lem:sieve`, `V` polynomial)

Correction supports `corr_{j₀}` (one block exact `e+1`, others `≤e`) give
`C_{j₀} = E_{j₀}∏_{k≠j₀}U_k = -∑_{corr_{j₀}}(-1)^{|d|}` (using even `h_j`
so `(-1)^{h_j+1} = -1`), hence
`V = U - ∑ C = ∑_U + ∑_{corr}` with `|coeff| = 1`, level `≤ z^{4h+2}`
(`corr_level_le`), and `sifted ≥ ∑ weight·Vval ≥ X·E[V] - remainderSum`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- Correction support for fixed `j₀`: exact `e+1` in `j₀`, `≤e` elsewhere. -/
def CorrSupport (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (j₀ : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun d =>
    (d ∩ B j₀).card = e j₀ + 1 ∧ ∀ j ∈ J, j ≠ j₀ → (d ∩ B j).card ≤ e j)

theorem mem_CorrSupport (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (j₀ : ℕ) (d : Finset ℕ) :
    d ∈ CorrSupport P J B e j₀ ↔ d ⊆ P ∧ (d ∩ B j₀).card = e j₀ + 1 ∧
      ∀ j ∈ J, j ≠ j₀ → (d ∩ B j).card ≤ e j := by
  simp only [CorrSupport, Finset.mem_filter, Finset.mem_powerset]

/-- `V` support: upper plus all corrections. -/
def SupportV (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) : Finset (Finset ℕ) :=
  Prelim.BlockSieve.SieveSupport P J B e ∪ J.biUnion (fun j₀ => CorrSupport P J B e j₀)

/-- Integer correction identity (pointwise `E·∏U = -∑_{corr}(-1)`). -/
theorem corr_integer_eq (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (bad : Finset ℕ) (j₀ : ℕ)
    (hbad : bad ⊆ P) (hcov : bad ⊆ J.biUnion B)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂))
    (hj₀ : j₀ ∈ J) (he₀ : Even (e j₀)) :
    ((bad ∩ B j₀).card.choose (e j₀ + 1) : ℤ)
      * ∏ j ∈ J.erase j₀,
        Prelim.SieveCalculus.blockUpper (e j) ((bad ∩ B j).card)
    = -∑ d ∈ (CorrSupport P J B e j₀).filter (· ⊆ bad),
        (-1 : ℤ) ^ d.card := by
  have hbad'_P : bad \ B j₀ ⊆ P :=
    Finset.Subset.trans Finset.sdiff_subset hbad
  have hcov' : bad \ B j₀ ⊆ (J.erase j₀).biUnion B := by
    intro p hp
    have hpmem : p ∈ bad := (Finset.mem_sdiff.mp hp).1
    have hpnot : p ∉ B j₀ := (Finset.mem_sdiff.mp hp).2
    have hcovp := hcov hpmem
    rw [Finset.mem_biUnion] at hcovp ⊢
    obtain ⟨j, hjJ, hjB⟩ := hcovp
    by_cases heq : j = j₀
    · subst heq
      exact absurd hjB hpnot
    · exact ⟨j, Finset.mem_erase.mpr ⟨heq, hjJ⟩, hjB⟩
  have hdisj' : ∀ j₁ ∈ J.erase j₀, ∀ j₂ ∈ J.erase j₀, j₁ ≠ j₂ →
      Disjoint (B j₁) (B j₂) :=
    fun j₁ h1 j₂ h2 hne => hdisj j₁ (Finset.mem_of_mem_erase h1)
      j₂ (Finset.mem_of_mem_erase h2) hne
  have hinter_eq : ∀ j ∈ J.erase j₀,
      ((bad \ B j₀) ∩ B j) = (bad ∩ B j) := by
    intro j hj
    have hjJ := Finset.mem_of_mem_erase hj
    have hjne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    have hD : Disjoint (B j₀) (B j) :=
      hdisj j₀ hj₀ j hjJ (fun heq => hjne heq.symm)
    ext p
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hpb, _⟩, hpj⟩
      exact ⟨hpb, hpj⟩
    · rintro ⟨hpb, hpj⟩
      refine ⟨⟨hpb, ?_⟩, hpj⟩
      intro hpa
      exact Prelim.BlockSieve.disjoint_mem_false hD hpa hpj
  have hprod_eq : ∏ j ∈ J.erase j₀,
      Prelim.SieveCalculus.blockUpper (e j) ((bad ∩ B j).card)
      = ∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
        (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card := by
    have hsupp := Prelim.BlockSieve.sieveSupport_sum_eq P (J.erase j₀) B e
      (bad \ B j₀) hbad'_P hcov' hdisj'
    have hcong : ∏ j ∈ J.erase j₀,
        Prelim.SieveCalculus.blockUpper (e j) ((bad ∩ B j).card)
        = ∏ j ∈ J.erase j₀,
          Prelim.SieveCalculus.blockUpper (e j) (((bad \ B j₀) ∩ B j).card) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hinter_eq j hj]
    rw [hcong]
    exact hsupp.symm
  have hE_eq : ((bad ∩ B j₀).card.choose (e j₀ + 1) : ℤ)
      = ∑ _u ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)), (1 : ℤ) := by
    have hcard : ((bad ∩ B j₀).powersetCard (e j₀ + 1)).card
        = (bad ∩ B j₀).card.choose (e j₀ + 1) :=
      Finset.card_powersetCard _ _
    calc ((bad ∩ B j₀).card.choose (e j₀ + 1) : ℤ)
        = (((((bad ∩ B j₀).powersetCard (e j₀ + 1)).card : ℕ)) : ℤ) := by
          rw [hcard]
      _ = ∑ _u ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)), (1 : ℤ) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro u _
          simp
  have hdouble : (∑ _u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1), (1 : ℤ))
      * (∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
        (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card)
      = ∑ u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1),
        ∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hdecomp : ((CorrSupport P J B e j₀).filter (· ⊆ bad))
      = ((((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
        ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀))).image
        (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)) := by
    ext d
    simp only [Finset.mem_image]
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdsupp, hdsub⟩ := hd
      rw [mem_CorrSupport] at hdsupp
      obtain ⟨hdP, hdEq, hdCon⟩ := hdsupp
      have huT : d ∩ B j₀ ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1) := by
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.inter_subset_inter hdsub (fun p hp => hp), ?_⟩
        rw [hdEq]
      have hvP : d \ B j₀ ∈ Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e := by
        rw [Prelim.BlockSieve.mem_sieveSupport]
        refine ⟨Finset.Subset.trans Finset.sdiff_subset hdP, fun j hj => ?_⟩
        have hjJ := Finset.mem_of_mem_erase hj
        have hjne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
        have hD : Disjoint (B j₀) (B j) :=
          hdisj j₀ hj₀ j hjJ (fun heq => hjne heq.symm)
        have hinter : (d \ B j₀) ∩ B j = d ∩ B j := by
          ext p
          simp only [Finset.mem_inter, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨hpd, _⟩, hpj⟩
            exact ⟨hpd, hpj⟩
          · rintro ⟨hpd, hpj⟩
            refine ⟨⟨hpd, ?_⟩, hpj⟩
            intro hpa
            exact Prelim.BlockSieve.disjoint_mem_false hD hpa hpj
        rw [hinter]
        exact hdCon j hjJ hjne
      have hvsub : d \ B j₀ ⊆ bad \ B j₀ := by
        intro p hp
        rw [Finset.mem_sdiff] at hp ⊢
        exact ⟨hdsub hp.1, hp.2⟩
      have hunion : d ∩ B j₀ ∪ d \ B j₀ = d := by
        ext p
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      exact ⟨(d ∩ B j₀, d \ B j₀),
        Finset.mem_product.mpr ⟨huT,
          Finset.mem_filter.mpr ⟨hvP, hvsub⟩⟩,
        hunion⟩
    · intro hd
      obtain ⟨uv, huv, heq⟩ := hd
      rw [Finset.mem_product] at huv
      obtain ⟨huU, huV⟩ := huv
      subst d
      rw [Finset.mem_filter] at huV
      obtain ⟨huVsup, huVsub⟩ := huV
      rw [Prelim.BlockSieve.mem_sieveSupport] at huVsup
      obtain ⟨huVP, huVcon⟩ := huVsup
      have huB : uv.1 ⊆ B j₀ :=
        Finset.Subset.trans (Finset.mem_powersetCard.mp huU).1
          Finset.inter_subset_right
      have hvD : Disjoint uv.2 (B j₀) := by
        rw [Finset.disjoint_left]
        intro p hpv hpa
        have hsub : uv.2 ⊆ bad \ B j₀ := huVsub
        exact (Finset.mem_sdiff.mp (hsub hpv)).2 hpa
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_CorrSupport]
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          rw [Finset.mem_union] at hp
          cases hp with
          | inl hpu =>
            have h1 : uv.1 ⊆ bad ∩ B j₀ :=
              Finset.mem_powersetCard.mp huU |>.1
            exact Finset.Subset.trans Finset.inter_subset_left hbad (h1 hpu)
          | inr hpv => exact huVP hpv
        · have hinter_a : (uv.1 ∪ uv.2) ∩ B j₀ = uv.1 := by
            ext p
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hp | hp, hpa⟩
              · exact hp
              · exact False.elim
                  (Prelim.BlockSieve.disjoint_mem_false hvD hp hpa)
            · intro hp
              exact ⟨Or.inl hp, huB hp⟩
          have hcard_u : uv.1.card = e j₀ + 1 :=
            (Finset.mem_powersetCard.mp huU).2
          rw [hinter_a, hcard_u]
        · intro j hj hjne
          have hD' : Disjoint (B j₀) (B j) :=
            hdisj j₀ hj₀ j hj (fun heq => hjne heq.symm)
          have hinter_j : (uv.1 ∪ uv.2) ∩ B j = uv.2 ∩ B j := by
            ext p
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hp | hp, hpj⟩
              · exact False.elim
                  (Prelim.BlockSieve.disjoint_mem_false hD' (huB hp) hpj)
              · exact ⟨hp, hpj⟩
            · rintro ⟨hpv, hpj⟩
              exact ⟨Or.inr hpv, hpj⟩
          rw [hinter_j]
          by_cases heq : j = j₀
          · subst heq
            exact absurd rfl hjne
          · have hj' : j ∈ J.erase j₀ := Finset.mem_erase.mpr ⟨heq, hj⟩
            exact huVcon j hj'
      · intro p hp
        rw [Finset.mem_union] at hp
        cases hp with
        | inl hpu =>
          have h1 : uv.1 ⊆ bad ∩ B j₀ :=
            Finset.mem_powersetCard.mp huU |>.1
          exact Finset.inter_subset_left (h1 hpu)
        | inr hpv =>
          exact Finset.sdiff_subset (huVsub hpv)
  have hinj : Set.InjOn (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)
      ↑(((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
        ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀))) := by
    intro uv huv uv' huv' heq
    have heq' : uv.1 ∪ uv.2 = uv'.1 ∪ uv'.2 := heq
    obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv)
    obtain ⟨hu1', hu2'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv')
    have huB : uv.1 ⊆ B j₀ :=
      Finset.Subset.trans (Finset.mem_powersetCard.mp hu1).1
        Finset.inter_subset_right
    have huB' : uv'.1 ⊆ B j₀ :=
      Finset.Subset.trans (Finset.mem_powersetCard.mp hu1').1
        Finset.inter_subset_right
    have hvD : Disjoint uv.2 (B j₀) := by
      have hsub : uv.2 ⊆ bad \ B j₀ :=
        (Finset.mem_filter.mp hu2).2
      exact Finset.disjoint_left.mpr (fun p hp =>
        (Finset.mem_sdiff.mp (hsub hp)).2)
    have hvD' : Disjoint uv'.2 (B j₀) := by
      have hsub : uv'.2 ⊆ bad \ B j₀ :=
        (Finset.mem_filter.mp hu2').2
      exact Finset.disjoint_left.mpr (fun p hp =>
        (Finset.mem_sdiff.mp (hsub hp)).2)
    have rec1 : uv.1 = (uv.1 ∪ uv.2) ∩ B j₀ := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inl hp, huB hp⟩
      · rintro ⟨hp | hp, hpa⟩
        · exact hp
        · exact False.elim (Prelim.BlockSieve.disjoint_mem_false hvD hp hpa)
    have rec1' : uv'.1 = (uv'.1 ∪ uv'.2) ∩ B j₀ := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inl hp, huB' hp⟩
      · rintro ⟨hp | hp, hpa⟩
        · exact hp
        · exact False.elim (Prelim.BlockSieve.disjoint_mem_false hvD' hp hpa)
    have rec2 : uv.2 = (uv.1 ∪ uv.2) \ B j₀ := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inr hp, fun h => Prelim.BlockSieve.disjoint_mem_false hvD hp h⟩
      · rintro ⟨hp | hp, hnb⟩
        · exact absurd (huB hp) hnb
        · exact hp
    have rec2' : uv'.2 = (uv'.1 ∪ uv'.2) \ B j₀ := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inr hp, fun h => Prelim.BlockSieve.disjoint_mem_false hvD' hp h⟩
      · rintro ⟨hp | hp, hnb⟩
        · exact absurd (huB' hp) hnb
        · exact hp
    have e1 : uv.1 = uv'.1 := by rw [rec1, rec1', heq']
    have e2 : uv.2 = uv'.2 := by rw [rec2, rec2', heq']
    exact Prod.ext e1 e2
  have hodd : Odd (e j₀ + 1) := he₀.add_one
  have hneg1 : (-1 : ℤ) ^ (e j₀ + 1) = -1 := hodd.neg_one_pow
  have hsign : ∀ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
      ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
        (· ⊆ bad \ B j₀)),
      (-1 : ℤ) ^ uv.2.card = -(-1 : ℤ) ^ ((uv.1 ∪ uv.2).card) := by
    intro uv huv
    obtain ⟨huU, _⟩ := Finset.mem_product.mp huv
    have huB : uv.1 ⊆ B j₀ :=
      Finset.Subset.trans (Finset.mem_powersetCard.mp huU).1
        Finset.inter_subset_right
    have hvD : Disjoint uv.1 uv.2 := by
      have hsub : uv.2 ⊆ bad \ B j₀ :=
        (Finset.mem_filter.mp (Finset.mem_product.mp huv).2).2
      rw [Finset.disjoint_left]
      intro p hpu hpv
      exact (Finset.mem_sdiff.mp (hsub hpv)).2 (huB hpu)
    have hcardU : uv.1.card = e j₀ + 1 := (Finset.mem_powersetCard.mp huU).2
    have hcard_union : (uv.1 ∪ uv.2).card = uv.1.card + uv.2.card :=
      Finset.card_union_of_disjoint hvD
    have hpow : (-1 : ℤ) ^ ((uv.1 ∪ uv.2).card)
        = (-1 : ℤ) ^ (e j₀ + 1) * (-1 : ℤ) ^ uv.2.card := by
      rw [hcard_union, hcardU, pow_add]
    rw [hpow, hneg1]
    ring
  have himg : ∑ d ∈ ((((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
      ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
        (· ⊆ bad \ B j₀))).image
      (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)),
      (-1 : ℤ) ^ d.card
      = ∑ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
        ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀)),
        (-1 : ℤ) ^ ((uv.1 ∪ uv.2).card) :=
    Finset.sum_image hinj
  have hprod_sum : (∑ _u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1), (1 : ℤ))
      * (∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
        (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card)
      = ∑ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
        ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀)), (-1 : ℤ) ^ uv.2.card := by
    have hmul : (∑ _u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1), (1 : ℤ))
        * (∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card)
        = ∑ u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1),
          ∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
            (· ⊆ bad \ B j₀), (1 : ℤ) * (-1 : ℤ) ^ v.card := by
      rw [Finset.sum_mul_sum]
    have hprod : ∑ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
        ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀)), (-1 : ℤ) ^ uv.2.card
        = ∑ u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1),
          ∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
            (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card :=
      Finset.sum_product _ _ _
    rw [hmul]
    rw [hprod]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  calc ((bad ∩ B j₀).card.choose (e j₀ + 1) : ℤ)
        * ∏ j ∈ J.erase j₀,
          Prelim.SieveCalculus.blockUpper (e j) ((bad ∩ B j).card)
      = (∑ _u ∈ (bad ∩ B j₀).powersetCard (e j₀ + 1), (1 : ℤ))
        * (∑ v ∈ (Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
          (· ⊆ bad \ B j₀), (-1 : ℤ) ^ v.card) := by
          rw [hE_eq, hprod_eq]
      _ = ∑ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
          ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
            (· ⊆ bad \ B j₀)), (-1 : ℤ) ^ uv.2.card := hprod_sum
      _ = ∑ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
          ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
            (· ⊆ bad \ B j₀)), -(-1 : ℤ) ^ ((uv.1 ∪ uv.2).card) := by
          apply Finset.sum_congr rfl
          intro uv huv
          exact hsign uv huv
      _ = -∑ uv ∈ ((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
          ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
            (· ⊆ bad \ B j₀)), (-1 : ℤ) ^ ((uv.1 ∪ uv.2).card) := by
          rw [Finset.sum_neg_distrib]
      _ = -∑ d ∈ ((((bad ∩ B j₀).powersetCard (e j₀ + 1)) ×ˢ
          ((Prelim.BlockSieve.SieveSupport P (J.erase j₀) B e).filter
            (· ⊆ bad \ B j₀))).image
          (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)),
          (-1 : ℤ) ^ d.card := by
          rw [himg]
      _ = -∑ d ∈ (CorrSupport P J B e j₀).filter (· ⊆ bad),
          (-1 : ℤ) ^ d.card := by
          rw [hdecomp]

/-- Real correction identity (cast of `corr_integer_eq`). -/
theorem corr_real_eq (P : Finset ℕ) (J : Finset ℕ)
    (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (bad : Finset ℕ) (j₀ : ℕ)
    (hbad : bad ⊆ P) (hcov : bad ⊆ J.biUnion B)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂))
    (hj₀ : j₀ ∈ J) (he₀ : Even (e j₀)) :
    Prelim.BlockSieve.blkE J B e bad j₀
      * ∏ k ∈ J.erase j₀, Prelim.BlockSieve.blkU J B e bad k
    = -∑ d ∈ (CorrSupport P J B e j₀).filter (· ⊆ bad),
        (-1 : ℝ) ^ d.card := by
  have hint := corr_integer_eq P J B e bad j₀ hbad hcov hdisj hj₀ he₀
  have hLHS : Prelim.BlockSieve.blkE J B e bad j₀
      * ∏ k ∈ J.erase j₀, Prelim.BlockSieve.blkU J B e bad k
      = ((((bad ∩ B j₀).card.choose (e j₀ + 1) : ℤ)
        * ∏ j ∈ J.erase j₀,
          Prelim.SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ) := by
    unfold Prelim.BlockSieve.blkE Prelim.BlockSieve.blkU
    push_cast
    ring
  have hRHS : (-∑ d ∈ (CorrSupport P J B e j₀).filter (· ⊆ bad),
        (-1 : ℝ) ^ d.card)
      = (((-∑ d ∈ (CorrSupport P J B e j₀).filter (· ⊆ bad),
        (-1 : ℤ) ^ d.card : ℤ)) : ℝ) := by
    push_cast
    ring
  rw [hLHS, hRHS, hint]

/-- Upper support disjoint from each correction (card `≤e` vs `=e+1`). -/
theorem disjoint_support_corr (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ J) :
    Disjoint (Prelim.BlockSieve.SieveSupport P J B e)
      (CorrSupport P J B e j₀) := by
  rw [Finset.disjoint_left]
  intro d hdU hdC
  have hU := (Prelim.BlockSieve.mem_sieveSupport P J B e d).mp hdU
  have hC := (mem_CorrSupport P J B e j₀ d).mp hdC
  have hle := hU.2 j₀ hj₀
  have heq := hC.2.1
  omega

/-- Two corrections are disjoint (`=e+1` in different blocks). -/
theorem disjoint_corr_corr (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (j₁ j₂ : ℕ) (hj₁ : j₁ ∈ J) (hj₂ : j₂ ∈ J) (hne : j₁ ≠ j₂) :
    Disjoint (CorrSupport P J B e j₁) (CorrSupport P J B e j₂) := by
  rw [Finset.disjoint_left]
  intro d hd1 hd2
  have h1 := (mem_CorrSupport P J B e j₁ d).mp hd1
  have h2 := (mem_CorrSupport P J B e j₂ d).mp hd2
  have heq : (d ∩ B j₁).card = e j₁ + 1 := h1.2.1
  have hle : (d ∩ B j₁).card ≤ e j₁ := h2.2.2 j₁ hj₁ hne
  omega

/-- Every `V`-support set lies in `P`. -/
theorem supportV_subset_P (P : Finset ℕ) (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV P J B e) : s ⊆ P := by
  unfold SupportV at hs
  rw [Finset.mem_union, Finset.mem_biUnion] at hs
  cases hs with
  | inl hU => exact (Prelim.BlockSieve.mem_sieveSupport P J B e s).mp hU |>.1
  | inr hC =>
    obtain ⟨j₀, _, hsC⟩ := hC
    exact (mem_CorrSupport P J B e j₀ s).mp hsC |>.1

/-- Every `V`-support set consists of primes (via `P ⊆ primes` hypothesis). -/
theorem supportV_subset_primes (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    s ⊆ S.primes :=
  (supportV_subset_P _ _ _ _ s hs).trans
    (biUnion_subset_primes α S z Jmax)

/-- `V`-support product recovers the set. -/
theorem supportV_prod_primeFactors (α : Type)
    (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    (∏ q ∈ s, q).primeFactors = s := by
  have hprimes : ∀ p ∈ s, p.Prime := by
    intro p hp
    exact S.prime p (supportV_subset_primes α S z Jmax h s hs hp)
  exact primeFactors_prod_eq s hprimes

/-- `V`-support product map is injective. -/
theorem supportV_prod_injOn (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) :
    Set.InjOn (fun s : Finset ℕ => ∏ q ∈ s, q)
      ↑(SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) := by
  intro s hs t ht heq
  have hs' := supportV_prod_primeFactors α S z Jmax h s (Finset.mem_coe.mp hs)
  have ht' := supportV_prod_primeFactors α S z Jmax h t (Finset.mem_coe.mp ht)
  have heq' : (∏ q ∈ s, q) = (∏ q ∈ t, q) := heq
  calc s = (∏ q ∈ s, q).primeFactors := hs'.symm
    _ = (∏ q ∈ t, q).primeFactors := by rw [heq']
    _ = t := ht'

/-- `V`-support level: every `s ∈ SupportV` has `(∏s:ℝ) ≤ z^{4h+2}`. -/
theorem supportV_level_le (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    ∏ p ∈ s, (p : ℝ) ≤ z ^ (4 * h + 2 : ℕ) := by
  unfold SupportV at hs
  rw [Finset.mem_union, Finset.mem_biUnion] at hs
  cases hs with
  | inl hU =>
    exact support_level_le α S z hz h Jmax s hU
  | inr hC =>
    obtain ⟨j₀, hj₀, hsC⟩ := hC
    have hmem := (mem_CorrSupport _ _ _ _ _ s).mp hsC
    obtain ⟨hdP, hdEq, hdCon⟩ := hmem
    exact corr_level_le α S z hz h Jmax j₀ hj₀ s hdP
      (fun j hj hjne => hdCon j hj hjne) hdEq

/-- Pointwise `V` equals the `SupportV` signed sum. -/
theorem Vval_eq_supportV_sum (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) (a : α) :
    Prelim.BlockSieve.Vval (Finset.range Jmax)
      (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
    = ∑ s ∈ (SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).filter
        (· ⊆ badFinset α S a), (-1 : ℝ) ^ s.card := by
  have hcov := badFinset_covered α S z hz Jmax hJ η C hdb a
  have hP : (badFinset α S a) ⊆
      (Finset.range Jmax).biUnion (fun j => Block α S z j) := hcov
  have hdisj : ∀ j₁ ∈ Finset.range Jmax, ∀ j₂ ∈ Finset.range Jmax, j₁ ≠ j₂ →
      Disjoint (Block α S z j₁) (Block α S z j₂) := by
    intro j₁ _ j₂ _ hne
    exact Block_disjoint α S z hz hne
  have heJ : ∀ j ∈ Finset.range Jmax, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  -- `U` part
  have hU := Uval_eq_support_sum α S z hz Jmax hJ η C hdb h a
  -- corrections
  have hC : ∀ j₀ ∈ Finset.range Jmax,
      Prelim.BlockSieve.blkE (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h)
        (badFinset α S a) j₀
      * ∏ k ∈ (Finset.range Jmax).erase j₀,
        Prelim.BlockSieve.blkU (Finset.range Jmax)
          (fun j => Block α S z j) (fun j => (j + 1) * h)
          (badFinset α S a) k
      = -∑ d ∈ (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₀).filter (· ⊆ badFinset α S a),
        (-1 : ℝ) ^ d.card := by
    intro j₀ hj₀
    have he0 : Even ((j₀ + 1) * h) := he.mul_left _
    exact corr_real_eq
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a) j₀
      hP hcov hdisj hj₀ he0
  -- `V = U - ∑ C`
  have hVdef : Prelim.BlockSieve.Vval (Finset.range Jmax)
      (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
      = Prelim.BlockSieve.Uval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
        - ∑ j₀ ∈ Finset.range Jmax,
          (Prelim.BlockSieve.blkE (Finset.range Jmax)
            (fun j => Block α S z j) (fun j => (j + 1) * h)
            (badFinset α S a) j₀
          * ∏ k ∈ (Finset.range Jmax).erase j₀,
            Prelim.BlockSieve.blkU (Finset.range Jmax)
              (fun j => Block α S z j) (fun j => (j + 1) * h)
              (badFinset α S a) k) := rfl
  rw [hVdef, hU]
  -- combine `∑_U + ∑_j ∑_{corr_j}`
  have hsum_corr : ∑ j₀ ∈ Finset.range Jmax,
      (Prelim.BlockSieve.blkE (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h)
        (badFinset α S a) j₀
        * ∏ k ∈ (Finset.range Jmax).erase j₀,
          Prelim.BlockSieve.blkU (Finset.range Jmax)
            (fun j => Block α S z j) (fun j => (j + 1) * h)
            (badFinset α S a) k)
      = -∑ j₀ ∈ Finset.range Jmax,
        ∑ d ∈ (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₀).filter (· ⊆ badFinset α S a),
        (-1 : ℝ) ^ d.card := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j₀ hj₀
    exact hC j₀ hj₀
  rw [hsum_corr, sub_neg_eq_add]
  -- `∑_U + ∑_j∑_{corr} = ∑_{SupportV.filter}`
  have hfilter_eq : ((SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h)).filter (· ⊆ badFinset α S a))
      = ((Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j)
        (fun j => (j + 1) * h)).filter (· ⊆ badFinset α S a))
        ∪ (Finset.range Jmax).biUnion (fun j₀ =>
          ((CorrSupport
            ((Finset.range Jmax).biUnion (fun j => Block α S z j))
            (Finset.range Jmax) (fun j => Block α S z j)
            (fun j => (j + 1) * h) j₀).filter (· ⊆ badFinset α S a))) := by
    ext d
    simp only [SupportV, Finset.mem_filter, Finset.mem_union,
      Finset.mem_biUnion]
    tauto
  -- disjointness of filtered parts
  have hdisjUf : Disjoint
      ((Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j)
        (fun j => (j + 1) * h)).filter (· ⊆ badFinset α S a))
      ((Finset.range Jmax).biUnion (fun j₀ =>
        (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₀).filter (· ⊆ badFinset α S a))) := by
    rw [Finset.disjoint_left]
    intro d hdU hdBi
    rw [Finset.mem_filter] at hdU
    obtain ⟨hdUsupp, _⟩ := hdU
    rw [Finset.mem_biUnion] at hdBi
    obtain ⟨j₀, hj₀, hdCfilt⟩ := hdBi
    rw [Finset.mem_filter] at hdCfilt
    obtain ⟨hdCsupp, _⟩ := hdCfilt
    have hD := disjoint_support_corr
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) j₀ hj₀
    have hempty : (Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h))
        ∩ (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₀) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hD
    have hmem : d ∈ (Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h))
        ∩ (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₀) :=
      Finset.mem_inter.mpr ⟨hdUsupp, hdCsupp⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty d hmem
  have hpairwise : Set.PairwiseDisjoint (↑(Finset.range Jmax) : Set ℕ)
      (fun j₀ => (CorrSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j)
        (fun j => (j + 1) * h) j₀).filter (· ⊆ badFinset α S a)) := by
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_filter] at hd1 hd2
    obtain ⟨hd1supp, _⟩ := hd1
    obtain ⟨hd2supp, _⟩ := hd2
    have hD := disjoint_corr_corr
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) j₁ j₂ hj₁ hj₂ hne
    have hempty : (CorrSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j)
        (fun j => (j + 1) * h) j₁)
        ∩ (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₂) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hD
    have hmem : d ∈ (CorrSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j)
        (fun j => (j + 1) * h) j₁)
        ∩ (CorrSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j)
          (fun j => (j + 1) * h) j₂) :=
      Finset.mem_inter.mpr ⟨hd1supp, hd2supp⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty d hmem
  rw [hfilter_eq, Finset.sum_union hdisjUf, Finset.sum_biUnion hpairwise]

/-- Weighted correction factorization (no `bad` filter). -/
theorem weighted_corr_eq (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (g : ℕ → ℝ) (j₀ : ℕ)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂))
    (hj₀ : j₀ ∈ J) (he₀ : Even (e j₀)) :
    ∑ s ∈ CorrSupport (J.biUnion B) J B e j₀,
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p
    = -(blockExpE (B j₀) g (e j₀)
      * ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)) := by
  have hdisj' : ∀ j₁ ∈ J.erase j₀, ∀ j₂ ∈ J.erase j₀, j₁ ≠ j₂ →
      Disjoint (B j₁) (B j₂) :=
    fun j₁ h1 j₂ h2 hne => hdisj j₁ (Finset.mem_of_mem_erase h1)
      j₂ (Finset.mem_of_mem_erase h2) hne
  -- `e` and `∏S` as symmetric sums
  have hE := blockExpE_eq_symm (B j₀) g (e j₀)
  have hS := support_weighted_sum_eq (J.erase j₀) B e g hdisj'
  -- full image `corr = image (powersetCard × supp')`
  have hdecomp : (CorrSupport (J.biUnion B) J B e j₀)
      = ((((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e)).image
        (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)) := by
    ext d
    simp only [Finset.mem_image]
    constructor
    · intro hd
      rw [mem_CorrSupport] at hd
      obtain ⟨hdP, hdEq, hdCon⟩ := hd
      have hu : d ∩ B j₀ ∈ (B j₀).powersetCard (e j₀ + 1) := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.inter_subset_right, hdEq⟩
      have hv : d \ B j₀ ∈ Prelim.BlockSieve.SieveSupport
          ((J.erase j₀).biUnion B) (J.erase j₀) B e := by
        rw [Prelim.BlockSieve.mem_sieveSupport]
        refine ⟨?_, fun j hj => ?_⟩
        · intro p hp
          have hpm := Finset.mem_sdiff.mp hp
          have hdPp := hdP hpm.1
          rw [Finset.mem_biUnion] at hdPp ⊢
          obtain ⟨j, hjJ, hjB⟩ := hdPp
          by_cases heq : j = j₀
          · subst heq
            exact absurd hjB hpm.2
          · exact ⟨j, Finset.mem_erase.mpr ⟨heq, hjJ⟩, hjB⟩
        · have hjJ := Finset.mem_of_mem_erase hj
          have hjne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
          have hD : Disjoint (B j₀) (B j) :=
            hdisj j₀ hj₀ j hjJ (fun heq => hjne heq.symm)
          have hinter : (d \ B j₀) ∩ B j = d ∩ B j := by
            ext p
            simp only [Finset.mem_inter, Finset.mem_sdiff]
            constructor
            · rintro ⟨⟨hpd, _⟩, hpj⟩
              exact ⟨hpd, hpj⟩
            · rintro ⟨hpd, hpj⟩
              refine ⟨⟨hpd, ?_⟩, hpj⟩
              intro hpa
              exact Prelim.BlockSieve.disjoint_mem_false hD hpa hpj
          rw [hinter]
          exact hdCon j hjJ hjne
      have hunion : d ∩ B j₀ ∪ d \ B j₀ = d := by
        ext p
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      exact ⟨(d ∩ B j₀, d \ B j₀),
        Finset.mem_product.mpr ⟨hu, hv⟩, hunion⟩
    · intro hd
      obtain ⟨uv, huv, heq⟩ := hd
      rw [Finset.mem_product] at huv
      obtain ⟨huU, huV⟩ := huv
      subst d
      rw [Prelim.BlockSieve.mem_sieveSupport] at huV
      obtain ⟨huVP, huVcon⟩ := huV
      have huB : uv.1 ⊆ B j₀ :=
        (Finset.mem_powersetCard.mp huU).1
      have huP : uv.1 ⊆ J.biUnion B :=
        Finset.Subset.trans huB
          (Finset.subset_biUnion_of_mem B hj₀)
      have hvP : uv.2 ⊆ J.biUnion B := by
        have hsub : (J.erase j₀).biUnion B ⊆ J.biUnion B := by
          rw [Finset.biUnion_subset]
          intro x hx
          exact Finset.subset_biUnion_of_mem B
            (Finset.mem_of_mem_erase hx)
        exact Finset.Subset.trans huVP hsub
      have hvD : Disjoint uv.2 (B j₀) := by
        rw [Finset.disjoint_left]
        intro p hpv hpa
        have hPp : p ∈ (J.erase j₀).biUnion B := huVP hpv
        rw [Finset.mem_biUnion] at hPp
        obtain ⟨j, hjJ, hjB⟩ := hPp
        have hjJ' := Finset.mem_of_mem_erase hjJ
        have hjne : j ≠ j₀ := (Finset.mem_erase.mp hjJ).1
        have hD : Disjoint (B j₀) (B j) :=
          hdisj j₀ hj₀ j hjJ' (fun heq => hjne heq.symm)
        exact Prelim.BlockSieve.disjoint_mem_false hD hpa hjB
      rw [mem_CorrSupport]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_union] at hp
        cases hp with
        | inl hpu => exact huP hpu
        | inr hpv => exact hvP hpv
      · have hinter_a : (uv.1 ∪ uv.2) ∩ B j₀ = uv.1 := by
          ext p
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hp | hp, hpa⟩
            · exact hp
            · exact False.elim
                (Prelim.BlockSieve.disjoint_mem_false hvD hp hpa)
          · intro hp
            exact ⟨Or.inl hp, huB hp⟩
        have hcard_u : uv.1.card = e j₀ + 1 :=
          (Finset.mem_powersetCard.mp huU).2
        rw [hinter_a, hcard_u]
      · intro j hj hjne
        have hD' : Disjoint (B j₀) (B j) :=
          hdisj j₀ hj₀ j hj (fun heq => hjne heq.symm)
        have hinter_j : (uv.1 ∪ uv.2) ∩ B j = uv.2 ∩ B j := by
          ext p
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hp | hp, hpj⟩
            · exact False.elim
                (Prelim.BlockSieve.disjoint_mem_false hD' (huB hp) hpj)
            · exact ⟨hp, hpj⟩
          · rintro ⟨hpv, hpj⟩
            exact ⟨Or.inr hpv, hpj⟩
        rw [hinter_j]
        by_cases heq : j = j₀
        · subst heq
          exact absurd rfl hjne
        · have hj' : j ∈ J.erase j₀ := Finset.mem_erase.mpr ⟨heq, hj⟩
          exact huVcon j hj'
  have hinj : Set.InjOn (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)
      ↑(((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e)) := by
    intro uv huv uv' huv' heq
    have heq' : uv.1 ∪ uv.2 = uv'.1 ∪ uv'.2 := heq
    obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv)
    obtain ⟨hu1', hu2'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv')
    have huB : uv.1 ⊆ B j₀ :=
      (Finset.mem_powersetCard.mp hu1).1
    have huB' : uv'.1 ⊆ B j₀ :=
      (Finset.mem_powersetCard.mp hu1').1
    have hvP : uv.2 ⊆ (J.erase j₀).biUnion B :=
      (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hu2 |>.1
    have hvP' : uv'.2 ⊆ (J.erase j₀).biUnion B :=
      (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hu2' |>.1
    have hvD : Disjoint uv.2 (B j₀) := by
      rw [Finset.disjoint_left]
      intro p hpv hpa
      have hPp : p ∈ (J.erase j₀).biUnion B := hvP hpv
      rw [Finset.mem_biUnion] at hPp
      obtain ⟨j, hjJ, hjB⟩ := hPp
      have hjJ' := Finset.mem_of_mem_erase hjJ
      have hjne : j ≠ j₀ := (Finset.mem_erase.mp hjJ).1
      have hD : Disjoint (B j₀) (B j) :=
        hdisj j₀ hj₀ j hjJ' (fun heq => hjne heq.symm)
      exact Prelim.BlockSieve.disjoint_mem_false hD hpa hjB
    have hvD' : Disjoint uv'.2 (B j₀) := by
      rw [Finset.disjoint_left]
      intro p hpv hpa
      have hPp : p ∈ (J.erase j₀).biUnion B := hvP' hpv
      rw [Finset.mem_biUnion] at hPp
      obtain ⟨j, hjJ, hjB⟩ := hPp
      have hjJ' := Finset.mem_of_mem_erase hjJ
      have hjne : j ≠ j₀ := (Finset.mem_erase.mp hjJ).1
      have hD : Disjoint (B j₀) (B j) :=
        hdisj j₀ hj₀ j hjJ' (fun heq => hjne heq.symm)
      exact Prelim.BlockSieve.disjoint_mem_false hD hpa hjB
    have rec1 : uv.1 = (uv.1 ∪ uv.2) ∩ B j₀ := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inl hp, huB hp⟩
      · rintro ⟨hp | hp, hpa⟩
        · exact hp
        · exact False.elim (Prelim.BlockSieve.disjoint_mem_false hvD hp hpa)
    have rec1' : uv'.1 = (uv'.1 ∪ uv'.2) ∩ B j₀ := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inl hp, huB' hp⟩
      · rintro ⟨hp | hp, hpa⟩
        · exact hp
        · exact False.elim (Prelim.BlockSieve.disjoint_mem_false hvD' hp hpa)
    have rec2 : uv.2 = (uv.1 ∪ uv.2) \ B j₀ := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inr hp, fun h => Prelim.BlockSieve.disjoint_mem_false hvD hp h⟩
      · rintro ⟨hp | hp, hnb⟩
        · exact absurd (huB hp) hnb
        · exact hp
    have rec2' : uv'.2 = (uv'.1 ∪ uv'.2) \ B j₀ := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inr hp, fun h => Prelim.BlockSieve.disjoint_mem_false hvD' hp h⟩
      · rintro ⟨hp | hp, hnb⟩
        · exact absurd (huB' hp) hnb
        · exact hp
    have e1 : uv.1 = uv'.1 := by rw [rec1, rec1', heq']
    have e2 : uv.2 = uv'.2 := by rw [rec2, rec2', heq']
    exact Prod.ext e1 e2
  have hodd : Odd (e j₀ + 1) := he₀.add_one
  have hneg1 : (-1 : ℝ) ^ (e j₀ + 1) = -1 := hodd.neg_one_pow
  -- double sum with weights
  have hE_rw : blockExpE (B j₀) g (e j₀)
      = ∑ u ∈ (B j₀).powersetCard (e j₀ + 1), ∏ p ∈ u, g p := by
    rw [hE]
  have hS_rw : ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)
      = ∑ v ∈ Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
        (J.erase j₀) B e, (-1 : ℝ) ^ v.card * ∏ p ∈ v, g p := by
    rw [hS]
  have hprod2 : (∑ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
      (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
        (J.erase j₀) B e),
      (((-1 : ℝ) ^ uv.2.card * (∏ p ∈ uv.1, g p)) * ∏ p ∈ uv.2, g p))
      = ∑ u ∈ (B j₀).powersetCard (e j₀ + 1),
        ∑ v ∈ Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e,
        (((-1 : ℝ) ^ (u, v).2.card * (∏ p ∈ (u, v).1, g p)) * ∏ p ∈ (u, v).2, g p) :=
    Finset.sum_product _ _ _
  have hprod : blockExpE (B j₀) g (e j₀)
      * ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)
      = ∑ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e),
        (((-1 : ℝ) ^ uv.2.card * (∏ p ∈ uv.1, g p)) * ∏ p ∈ uv.2, g p) := by
    rw [hE_rw, hS_rw, Finset.sum_mul_sum, hprod2]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    have h1 : ((u, v).1) = u := rfl
    have h2 : ((u, v).2) = v := rfl
    rw [h1, h2]
    ring
  have hsign_w : ∀ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
      (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
        (J.erase j₀) B e),
      (-1 : ℝ) ^ uv.2.card * ((∏ p ∈ uv.1, g p) * (∏ p ∈ uv.2, g p))
      = -(((-1 : ℝ) ^ ((uv.1 ∪ uv.2).card)) * (∏ p ∈ uv.1 ∪ uv.2, g p)) := by
    intro uv huv
    obtain ⟨huU, huV⟩ := Finset.mem_product.mp huv
    have huB : uv.1 ⊆ B j₀ := (Finset.mem_powersetCard.mp huU).1
    have hvP : uv.2 ⊆ (J.erase j₀).biUnion B :=
      (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp huV |>.1
    have hdisjUV : Disjoint uv.1 uv.2 := by
      rw [Finset.disjoint_left]
      intro p hpu hpv
      have hpa := huB hpu
      have hPp : p ∈ (J.erase j₀).biUnion B := hvP hpv
      rw [Finset.mem_biUnion] at hPp
      obtain ⟨j, hjJ, hjB⟩ := hPp
      have hjJ' := Finset.mem_of_mem_erase hjJ
      have hjne : j ≠ j₀ := (Finset.mem_erase.mp hjJ).1
      have hD : Disjoint (B j₀) (B j) :=
        hdisj j₀ hj₀ j hjJ' (fun heq => hjne heq.symm)
      exact Prelim.BlockSieve.disjoint_mem_false hD hpa hjB
    have hcardU : uv.1.card = e j₀ + 1 := (Finset.mem_powersetCard.mp huU).2
    have hcardUunion : (uv.1 ∪ uv.2).card = uv.1.card + uv.2.card :=
      Finset.card_union_of_disjoint hdisjUV
    have hprodU : ∏ p ∈ uv.1 ∪ uv.2, g p
        = (∏ p ∈ uv.1, g p) * ∏ p ∈ uv.2, g p :=
      Finset.prod_union hdisjUV
    have hpow : (-1 : ℝ) ^ ((uv.1 ∪ uv.2).card)
        = (-1 : ℝ) ^ (e j₀ + 1) * (-1 : ℝ) ^ uv.2.card := by
      rw [hcardUunion, hcardU, pow_add]
    rw [hpow, hneg1, hprodU]
    ring
  have himg_w : ∑ d ∈ ((((B j₀).powersetCard (e j₀ + 1)) ×ˢ
      (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
        (J.erase j₀) B e)).image
      (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)),
      (-1 : ℝ) ^ d.card * ∏ p ∈ d, g p
      = ∑ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e),
        (-1 : ℝ) ^ ((uv.1 ∪ uv.2).card) * ∏ p ∈ uv.1 ∪ uv.2, g p :=
    Finset.sum_image hinj
  calc ∑ s ∈ CorrSupport (J.biUnion B) J B e j₀,
        (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p
      = ∑ d ∈ ((((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e)).image
        (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)),
        (-1 : ℝ) ^ d.card * ∏ p ∈ d, g p := by
        rw [hdecomp]
    _ = ∑ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e),
        (-1 : ℝ) ^ ((uv.1 ∪ uv.2).card) * ∏ p ∈ uv.1 ∪ uv.2, g p := himg_w
    _ = ∑ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e),
        -((-1 : ℝ) ^ uv.2.card * ((∏ p ∈ uv.1, g p) * (∏ p ∈ uv.2, g p))) := by
        apply Finset.sum_congr rfl
        intro uv huv
        have h := hsign_w uv huv
        linarith
    _ = -(∑ uv ∈ ((B j₀).powersetCard (e j₀ + 1)) ×ˢ
        (Prelim.BlockSieve.SieveSupport ((J.erase j₀).biUnion B)
          (J.erase j₀) B e),
        (-1 : ℝ) ^ uv.2.card * ((∏ p ∈ uv.1, g p) * (∏ p ∈ uv.2, g p))) := by
        rw [Finset.sum_neg_distrib]
    _ = -(blockExpE (B j₀) g (e j₀)
        * ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)) := by
        rw [hprod]
        congr 1
        apply Finset.sum_congr rfl
        intro uv huv
        ring

/-- Monomial at `∏ s` equals the subset indicator, for `s ∈ SupportV`. -/
theorem monomial_eq_subsetV (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h))
    (a : α) :
    S.monomial (∏ q ∈ s, q) a
      = (if s ⊆ badFinset α S a then (1 : ℝ) else 0) := by
  have hpf := supportV_prod_primeFactors α S z Jmax h s hs
  unfold Erdos821.Blueprint.SieveData.monomial
  have hequiv : (∀ p ∈ (∏ q ∈ s, q).primeFactors, S.bad p a)
      ↔ s ⊆ badFinset α S a := by
    constructor
    · intro hall p hpmem
      have hmem : p ∈ (∏ q ∈ s, q).primeFactors := hpf.symm ▸ hpmem
      have hbad := hall p hmem
      rw [mem_badFinset]
      exact ⟨supportV_subset_primes α S z Jmax h s hs hpmem, hbad⟩
    · intro hsub p hpmem
      have hmem : p ∈ s := hpf ▸ hpmem
      have hmem2 := hsub hmem
      exact (mem_badFinset α S a p).mp hmem2 |>.2
  simp only [hequiv]

/-- Density at `∏ s` factorizes, for `s ∈ SupportV`. -/
theorem g_prod_eqV (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    S.g (∏ q ∈ s, q) = ∏ p ∈ s, S.density p := by
  unfold Erdos821.Blueprint.SieveData.g
  rw [supportV_prod_primeFactors α S z Jmax h s hs]

/-- Pointwise lower: `weight·Vval ≤` sifted term. -/
theorem sifted_term_ge_Vval (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) (a : α) (ha : a ∈ S.objects) :
    S.weight a * Prelim.BlockSieve.Vval (Finset.range Jmax)
      (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
      ≤ (if ∀ p ∈ S.primes, ¬ S.bad p a then S.weight a else 0) := by
  rw [sifted_term_eq]
  have hcov := badFinset_covered α S z hz Jmax hJ η C hdb a
  have heJ : ∀ j ∈ Finset.range Jmax, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  have hVI := Prelim.BlockSieve.Vval_le_avoid (Finset.range Jmax)
    (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a) hcov heJ
  have hw := S.nonneg a ha
  by_cases hempty : badFinset α S a = ∅
  · have hif : (if badFinset α S a = ∅ then (1 : ℝ) else 0) = 1 :=
      if_pos hempty
    have hgoal : S.weight a * (if badFinset α S a = ∅ then (1 : ℝ) else 0)
        = S.weight a * 1 := by rw [hif]
    rw [hgoal]
    have hVI1 : Prelim.BlockSieve.Vval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
        ≤ 1 := by
      have h2 := hVI
      rw [hif] at h2
      exact h2
    exact mul_le_mul_of_nonneg_left hVI1 hw
  · have hif : (if badFinset α S a = ∅ then (1 : ℝ) else 0) = 0 :=
      if_neg hempty
    have hgoal : S.weight a * (if badFinset α S a = ∅ then (1 : ℝ) else 0)
        = 0 := by rw [hif, mul_zero]
    rw [hgoal]
    -- `V ≤ 0` when some bad prime exists: `V ≤ I = 0`
    have hVI0 : Prelim.BlockSieve.Vval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
        ≤ 0 := by
      have h2 := hVI
      rw [hif] at h2
      exact h2
    exact mul_nonpos_of_nonneg_of_nonpos hw hVI0

/-- Global lower: `∑ weight·Vval ≤ sifted`. -/
theorem sifted_ge_sum_Vval (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) :
    ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Vval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a) ≤ S.sifted := by
  unfold Erdos821.Blueprint.SieveData.sifted
  apply Finset.sum_le_sum
  intro a ha
  exact sifted_term_ge_Vval α S z hz Jmax hJ η C hdb h he a ha

/-- Weighted lower sum as a double sum. -/
theorem sum_Vval_eq_double (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C) (h : ℕ) (he : Even h) :
    ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Vval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a)
    = ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
      ∑ a ∈ S.objects,
        (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0) := by
  have hVval : ∀ a ∈ S.objects,
      S.weight a * Prelim.BlockSieve.Vval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
      = ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0) := by
    intro a _
    rw [Vval_eq_supportV_sum α S z hz Jmax hJ η C hdb h he a, Finset.mul_sum]
    exact Finset.sum_filter (fun s => s ⊆ badFinset α S a)
      (fun s => S.weight a * (-1 : ℝ) ^ s.card)
  have hstep : ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Vval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a)
      = ∑ a ∈ S.objects, ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0) :=
    Finset.sum_congr rfl (fun a ha => hVval a ha)
  rw [hstep]
  exact Finset.sum_comm

/-- Inner sum equals `(-1)^{|s|}·(X·g + r)` for `s ∈ SupportV`. -/
theorem inner_sum_eqV (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    ∑ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
    = (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q) + S.remainder (∏ q ∈ s, q)) := by
  have hmon : ∀ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a else 0)
      = S.weight a * S.monomial (∏ q ∈ s, q) a := by
    intro a _
    rw [monomial_eq_subsetV α S z Jmax h s hs a]
    by_cases hsub : s ⊆ badFinset α S a <;> simp [hsub]
  have hG : ∀ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
      = (-1 : ℝ) ^ s.card * (if s ⊆ badFinset α S a then S.weight a else 0) := by
    intro a _
    by_cases hsub : s ⊆ badFinset α S a <;> simp [hsub, mul_comm]
  have hsum1 : ∑ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
      = (-1 : ℝ) ^ s.card * ∑ a ∈ S.objects,
        (if s ⊆ badFinset α S a then S.weight a else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact hG a ha
  have hsum2 : ∑ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a else 0)
      = ∑ a ∈ S.objects, S.weight a * S.monomial (∏ q ∈ s, q) a := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hmon a ha
  have hsum3 : ∑ a ∈ S.objects, S.weight a * S.monomial (∏ q ∈ s, q) a
      = S.X * S.g (∏ q ∈ s, q) + S.remainder (∏ q ∈ s, q) := by
    have hdef : S.remainder (∏ q ∈ s, q)
        = (∑ a ∈ S.objects, S.weight a * S.monomial (∏ q ∈ s, q) a)
          - S.X * S.g (∏ q ∈ s, q) := rfl
    linarith
  rw [hsum1, hsum2, hsum3]

/-- `SupportV` image lies in `products D` (`D = z^{4h+2}`). -/
theorem supportV_image_subset (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax h : ℕ)
    (D : ℝ) (hD : D = z ^ (4 * h + 2 : ℕ)) :
    (SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).image
      (fun s : Finset ℕ => ∏ q ∈ s, q)
    ⊆ S.products D := by
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  have hsq := prod_primes_squarefree s
    (fun p hp => S.prime p (supportV_subset_primes α S z Jmax h s hs hp))
  have hpf := supportV_prod_primeFactors α S z Jmax h s hs
  have hprimes : (∏ q ∈ s, q).primeFactors ⊆ S.primes := by
    rw [hpf]
    exact supportV_subset_P _ _ _ _ s hs |>.trans
      (biUnion_subset_primes α S z Jmax)
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
  have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
  have hlevel : ((∏ q ∈ s, q : ℕ) : ℝ) ≤ D := by
    have hle := supportV_level_le α S z hz Jmax h s hs
    have hcast : ((∏ q ∈ s, q : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := Nat.cast_prod _ _
    rw [hcast, hD]
    exact hle
  have hd1 : 1 ≤ ∏ q ∈ s, q := by
    apply Finset.one_le_prod
    intro p hp
    exact (S.prime p (supportV_subset_primes α S z Jmax h s hs hp)).pos
  have hdle : ∏ q ∈ s, q ≤ ⌊D⌋₊ :=
    Nat.le_floor hlevel
  unfold Erdos821.Blueprint.SieveData.products
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hd1, hdle⟩, hsq, hprimes⟩

/-- Lower counting: `X·E[V] - remainderSum ≤ sifted`. -/
theorem sifted_ge_main_sub_remainder (α : Type)
    (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) :
    S.X * (∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * ∏ p ∈ s, S.density p)
      - S.remainderSum (z ^ (4 * h + 2 : ℕ)) ≤ S.sifted := by
  have hsupp_ge := sifted_ge_sum_Vval α S z hz Jmax hJ η C hdb h he
  have hdouble := sum_Vval_eq_double α S z hz Jmax hJ η C hdb h he
  have hmain : ∑ s ∈ SupportV
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
      (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
      = S.X * (∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * ∏ p ∈ s, S.density p) := by
    have hg : ∀ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        S.g (∏ q ∈ s, q) = ∏ p ∈ s, S.density p := by
      intro s hs
      exact g_prod_eqV α S z Jmax h s hs
    have hsum_eq : ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
        = S.X * ∑ s ∈ SupportV
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          ((-1 : ℝ) ^ s.card * ∏ p ∈ s, S.density p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hg s hs]
      ring
    rw [hsum_eq]
  have hcombine : ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Vval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a)
      = S.X * (∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * ∏ p ∈ s, S.density p)
        + ∑ s ∈ SupportV
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q) := by
    rw [hdouble]
    have hinner : ∀ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        ∑ a ∈ S.objects,
          (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
        = (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
          + (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q) := by
      intro s hs
      have h1 := inner_sum_eqV α S z Jmax h s hs
      rw [h1, mul_add]
    have h1 : ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        ∑ a ∈ S.objects,
          (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
        = ∑ s ∈ SupportV
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          ((-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
            + (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q)) :=
      Finset.sum_congr rfl (fun s hs => hinner s hs)
    rw [h1, Finset.sum_add_distrib, hmain]
  have hrem_ge : -(S.remainderSum (z ^ (4 * h + 2 : ℕ)))
      ≤ ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q) := by
    have hterm : ∀ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        -|S.remainder (∏ q ∈ s, q)|
        ≤ (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q) := by
      intro s _
      rcases neg_one_pow_eq_or (R := ℝ) s.card with h1 | h1
      · rw [h1, one_mul]
        linarith [neg_le_abs (S.remainder (∏ q ∈ s, q))]
      · rw [h1, neg_one_mul]
        linarith [le_abs_self (S.remainder (∏ q ∈ s, q))]
    have hsum_neg : ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q)
        ≥ ∑ s ∈ SupportV
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          -|S.remainder (∏ q ∈ s, q)| := by
      apply Finset.sum_le_sum
      intro s hs
      exact hterm s hs
    have himage_eq : ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        |S.remainder (∏ q ∈ s, q)|
        = ∑ d ∈ (SupportV
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).image
          (fun s : Finset ℕ => ∏ q ∈ s, q),
          |S.remainder d| := by
      rw [Finset.sum_image]
      intro s hs t ht heq
      exact supportV_prod_injOn α S z Jmax h
        (Finset.mem_coe.mpr hs) (Finset.mem_coe.mpr ht) heq
    have hsub := supportV_image_subset α S z hz Jmax h
      (z ^ (4 * h + 2 : ℕ)) rfl
    have hle_image : ∑ d ∈ (SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).image
        (fun s : Finset ℕ => ∏ q ∈ s, q), |S.remainder d|
        ≤ ∑ d ∈ S.products (z ^ (4 * h + 2 : ℕ)), |S.remainder d| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro d _ _
      exact abs_nonneg _
    have hremainder : S.remainderSum (z ^ (4 * h + 2 : ℕ))
        = ∑ d ∈ S.products (z ^ (4 * h + 2 : ℕ)), |S.remainder d| := rfl
    have hneg_sum : ∑ s ∈ SupportV
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        -|S.remainder (∏ q ∈ s, q)|
        = -(∑ s ∈ SupportV
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          |S.remainder (∏ q ∈ s, q)|) := by
      rw [Finset.sum_neg_distrib]
    linarith [hsum_neg, himage_eq, hle_image, hremainder, hneg_sum]
  linarith [hsupp_ge, hcombine, hrem_ge]

/-- Weighted `V` expectation: `∑_{SupportV} = ∏S - ∑ corr`. -/
theorem weighted_V_eq (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (g : ℕ → ℝ)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂))
    (heven : ∀ j₀ ∈ J, Even (e j₀)) :
    ∑ s ∈ SupportV (J.biUnion B) J B e,
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p
    = (∏ j ∈ J, blockExpS (B j) g (e j))
      - ∑ j₀ ∈ J, (blockExpE (B j₀) g (e j₀)
        * ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)) := by
  have hU := support_weighted_sum_eq J B e g hdisj
  have hC : ∀ j₀ ∈ J,
      ∑ s ∈ CorrSupport (J.biUnion B) J B e j₀,
        (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p
      = -(blockExpE (B j₀) g (e j₀)
        * ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)) := by
    intro j₀ hj₀
    exact weighted_corr_eq J B e g j₀ hdisj hj₀ (heven j₀ hj₀)
  have hdisjU : Disjoint
      (Prelim.BlockSieve.SieveSupport (J.biUnion B) J B e)
      (J.biUnion (fun j₀ => CorrSupport (J.biUnion B) J B e j₀)) := by
    rw [Finset.disjoint_left]
    intro d hdU hdBi
    rw [Finset.mem_biUnion] at hdBi
    obtain ⟨j₀, hj₀, hdC⟩ := hdBi
    exact Finset.disjoint_left.mp
      (disjoint_support_corr (J.biUnion B) J B e j₀ hj₀) hdU hdC
  have hpair : Set.PairwiseDisjoint (↑J : Set ℕ)
      (fun j₀ => CorrSupport (J.biUnion B) J B e j₀) := by
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    simp only [Function.onFun]
    exact disjoint_corr_corr (J.biUnion B) J B e j₁ j₂ hj₁ hj₂ hne
  have hsum : ∑ s ∈ SupportV (J.biUnion B) J B e,
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p
      = (∑ s ∈ Prelim.BlockSieve.SieveSupport (J.biUnion B) J B e,
        (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p)
        + ∑ j₀ ∈ J, ∑ s ∈ CorrSupport (J.biUnion B) J B e j₀,
          (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p := by
    unfold SupportV
    rw [Finset.sum_union hdisjU, Finset.sum_biUnion hpair]
  rw [hsum, hU]
  have hcorr : (∑ j₀ ∈ J, ∑ s ∈ CorrSupport (J.biUnion B) J B e j₀,
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p)
      = ∑ j₀ ∈ J, -(blockExpE (B j₀) g (e j₀)
        * ∏ j ∈ J.erase j₀, blockExpS (B j) g (e j)) :=
    Finset.sum_congr rfl (fun j₀ hj₀ => hC j₀ hj₀)
  rw [hcorr, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Weighted `V` expectation as `∏S - corrExp`. -/
theorem weighted_V_eq_corrExp (N h : ℕ) (B : ℕ → Finset ℕ) (g : ℕ → ℝ)
    (hdisj : ∀ j₁ ∈ Finset.range N, ∀ j₂ ∈ Finset.range N, j₁ ≠ j₂ →
      Disjoint (B j₁) (B j₂))
    (he : Even h) :
    ∑ s ∈ SupportV ((Finset.range N).biUnion B) (Finset.range N) B
      (fun j => (j + 1) * h),
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, g p
    = (∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h))
      - corrExp N B g h := by
  have hgen := weighted_V_eq (Finset.range N) B (fun j => (j + 1) * h) g
    hdisj (fun j₀ _ => he.mul_left _)
  rw [hgen]
  rfl

end PrelimLemmas
end Erdos821
