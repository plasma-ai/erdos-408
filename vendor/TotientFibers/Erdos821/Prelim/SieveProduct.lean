import Mathlib
import Erdos821.Prelim.BlockSieve
import Erdos821.Prelim.SieveExpectation

/-!
# Sieve products: weighted support sums factorize (`lem:sieve`)

For disjoint blocks `B_j`, `j ∈ J`, with caps `e_j` and densities `g`,
`∑_{d} (-1)^{|d|} ∏_d g = ∏_j S_j` where `S_j` is the one-block signed sum
(`PrelimLemmas.blockExpS`, via `blockExpS_eq_symm`). Induction as in
`Prelim.BlockSieve.sieveSupport_sum_eq` (image decomposition
`d = (d∩B_a) ∪ (d\\B_a)`, `InjOn`, double sums with `pow_add` for `(-1)`
and `prod_union` for `∏ g`), with ambient `J.biUnion B` (so base `J=∅`
gives `{∅}`).
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- Weighted support sum factorizes as a product of block expectations. -/
theorem support_weighted_sum_eq (J : Finset ℕ) (B : ℕ → Finset ℕ)
    (e : ℕ → ℕ) (g : ℕ → ℝ)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂)) :
    (∑ d ∈ Prelim.BlockSieve.SieveSupport (J.biUnion B) J B e,
      (-1 : ℝ) ^ d.card * ∏ p ∈ d, g p)
      = ∏ j ∈ J, blockExpS (B j) g (e j) := by
  induction J using Finset.induction with
  | empty =>
    have hset : Prelim.BlockSieve.SieveSupport ((∅ : Finset ℕ).biUnion B) ∅ B e
        = {∅} := by
      ext d
      simp only [Prelim.BlockSieve.SieveSupport, Finset.mem_filter,
        Finset.mem_powerset, Finset.mem_singleton, Finset.biUnion_empty]
      constructor
      · rintro ⟨hsub, -⟩
        exact Finset.subset_empty.mp hsub
      · intro heq
        subst heq
        exact ⟨Finset.empty_subset _, fun j hj => absurd hj (Finset.notMem_empty j)⟩
    rw [hset, Finset.sum_singleton, Finset.prod_empty]
    simp
  | @insert a s has ih =>
    have hdisj' : ∀ j₁ ∈ s, ∀ j₂ ∈ s, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂) :=
      fun j₁ h1 j₂ h2 hne =>
        hdisj j₁ (Finset.mem_insert_of_mem h1) j₂ (Finset.mem_insert_of_mem h2) hne
    have ih' := ih hdisj'
    -- unions
    have hP : (insert a s).biUnion B = B a ∪ s.biUnion B := Finset.biUnion_insert
    have hdisjPs : Disjoint (B a) (s.biUnion B) := by
      rw [Finset.disjoint_left]
      intro p hpa hpP
      rw [Finset.mem_biUnion] at hpP
      obtain ⟨j, hjJ, hjB⟩ := hpP
      have hne : a ≠ j := fun heq => has (heq ▸ hjJ)
      exact (Finset.disjoint_left.mp
        (hdisj a (Finset.mem_insert_self a s) j
          (Finset.mem_insert_of_mem hjJ) hne)) hpa hjB
    -- one-block factor is `blockExpS`
    have ha_side : (∑ u ∈ (B a).powerset.filter (fun u => u.card ≤ e a),
          (-1 : ℝ) ^ u.card * ∏ p ∈ u, g p)
        = blockExpS (B a) g (e a) :=
      (blockExpS_eq_symm (B a) g (e a)).symm
    have hprod : (∏ j ∈ insert a s, blockExpS (B j) g (e j))
        = blockExpS (B a) g (e a) * ∏ j ∈ s, blockExpS (B j) g (e j) := by
      rw [Finset.prod_insert has]
    -- decomposition as image
    have hdecomp : Prelim.BlockSieve.SieveSupport ((insert a s).biUnion B)
          (insert a s) B e
        = ((((B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
            (Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e)).image
            (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)) := by
      ext d
      simp only [Finset.mem_image]
      constructor
      · intro hd
        rw [Prelim.BlockSieve.mem_sieveSupport] at hd
        obtain ⟨hdP, hcon⟩ := hd
        refine ⟨(d ∩ B a, d \ B a), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_powerset.mpr
            (Finset.inter_subset_right), hcon a (Finset.mem_insert_self a s)⟩
        · rw [Prelim.BlockSieve.mem_sieveSupport]
          refine ⟨?_, fun j hj => ?_⟩
          · intro p hp
            have hpm := Finset.mem_sdiff.mp hp
            have hdPp := hdP hpm.1
            rw [hP] at hdPp
            simp only [Finset.mem_union, Finset.mem_biUnion] at hdPp ⊢
            cases hdPp with
            | inl hpa => exact absurd hpa hpm.2
            | inr hrest => exact hrest
          · have hinter : (d \ B a) ∩ B j = d ∩ B j := by
              ext p
              simp only [Finset.mem_inter, Finset.mem_sdiff]
              constructor
              · rintro ⟨⟨hpd, -⟩, hpj⟩
                exact ⟨hpd, hpj⟩
              · rintro ⟨hpd, hpj⟩
                refine ⟨⟨hpd, ?_⟩, hpj⟩
                intro hpa
                have hdisjaj : Disjoint (B a) (B j) :=
                  hdisj a (Finset.mem_insert_self a s) j
                    (Finset.mem_insert_of_mem hj)
                    (fun heq => has (heq.symm ▸ hj))
                exact Prelim.BlockSieve.disjoint_mem_false hdisjaj hpa hpj
            rw [hinter]
            exact hcon j (Finset.mem_insert_of_mem hj)
        · show d ∩ B a ∪ d \ B a = d
          ext p
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          tauto
      · intro hd
        obtain ⟨uv, huv, heq⟩ := hd
        rw [Finset.mem_product] at huv
        obtain ⟨huU, huV⟩ := huv
        subst d
        rw [Prelim.BlockSieve.mem_sieveSupport] at huV ⊢
        obtain ⟨huVP, huVcon⟩ := huV
        rw [Finset.mem_filter] at huU
        obtain ⟨huUp, huC⟩ := huU
        have huB : uv.1 ⊆ B a := Finset.mem_powerset.mp huUp
        have hvD : Disjoint uv.2 (B a) := by
          rw [Finset.disjoint_left]
          intro p hpv hpa
          have hPp : p ∈ s.biUnion B := huVP hpv
          rw [Finset.mem_biUnion] at hPp
          obtain ⟨j, hjJ, hjB⟩ := hPp
          have hdisjaj : Disjoint (B a) (B j) :=
            hdisj a (Finset.mem_insert_self a s) j
              (Finset.mem_insert_of_mem hjJ)
              (fun heq => has (heq.symm ▸ hjJ))
          exact Prelim.BlockSieve.disjoint_mem_false hdisjaj hpa hjB
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [Finset.mem_union] at hp
          cases hp with
          | inl hpu => rw [hP]; exact Finset.mem_union.mpr (Or.inl (huB hpu))
          | inr hpv =>
            have := huVP hpv
            rw [hP]
            exact Finset.mem_union.mpr (Or.inr this)
        · intro j hj
          rw [Finset.mem_insert] at hj
          cases hj with
          | inl hja =>
            subst j
            have hinter_a : (uv.1 ∪ uv.2) ∩ B a = uv.1 := by
              ext p
              simp only [Finset.mem_inter, Finset.mem_union]
              constructor
              · rintro ⟨hp | hp, hpa⟩
                · exact hp
                · exact False.elim
                    (Prelim.BlockSieve.disjoint_mem_false hvD hp hpa)
              · intro hp
                exact ⟨Or.inl hp, huB hp⟩
            rw [hinter_a]
            exact huC
          | inr hjs =>
            have hdisjaj : Disjoint (B a) (B j) :=
              hdisj a (Finset.mem_insert_self a s) j
                (Finset.mem_insert_of_mem hjs)
                (fun heq => has (heq.symm ▸ hjs))
            have hinter_j : (uv.1 ∪ uv.2) ∩ B j = uv.2 ∩ B j := by
              ext p
              simp only [Finset.mem_inter, Finset.mem_union]
              constructor
              · rintro ⟨hp | hp, hpj⟩
                · exact False.elim
                    (Prelim.BlockSieve.disjoint_mem_false hdisjaj (huB hp) hpj)
                · exact ⟨hp, hpj⟩
              · rintro ⟨hpv, hpj⟩
                exact ⟨Or.inr hpv, hpj⟩
            rw [hinter_j]
            exact huVcon j hjs
    have hinj : Set.InjOn (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)
        ↑((((B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
          (Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e))) := by
      intro uv huv uv' huv' heq
      have heq' : uv.1 ∪ uv.2 = uv'.1 ∪ uv'.2 := heq
      obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv)
      obtain ⟨hu1', hu2'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv')
      have huB : uv.1 ⊆ B a := by
        have hsub : uv.1 ⊆ B a :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hu1).1
        exact hsub
      have huB' : uv'.1 ⊆ B a := by
        have hsub : uv'.1 ⊆ B a :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hu1').1
        exact hsub
      have hvP : uv.2 ⊆ s.biUnion B :=
        (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hu2 |>.1
      have hvP' : uv'.2 ⊆ s.biUnion B :=
        (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hu2' |>.1
      have hvD : Disjoint uv.2 (B a) := by
        rw [Finset.disjoint_left]
        intro p hpv hpa
        have hPp : p ∈ s.biUnion B := hvP hpv
        rw [Finset.mem_biUnion] at hPp
        obtain ⟨j, hjJ, hjB⟩ := hPp
        have hdisjaj : Disjoint (B a) (B j) :=
          hdisj a (Finset.mem_insert_self a s) j
            (Finset.mem_insert_of_mem hjJ) (fun heq => has (heq.symm ▸ hjJ))
        exact Prelim.BlockSieve.disjoint_mem_false hdisjaj hpa hjB
      have hvD' : Disjoint uv'.2 (B a) := by
        rw [Finset.disjoint_left]
        intro p hpv hpa
        have hPp : p ∈ s.biUnion B := hvP' hpv
        rw [Finset.mem_biUnion] at hPp
        obtain ⟨j, hjJ, hjB⟩ := hPp
        have hdisjaj : Disjoint (B a) (B j) :=
          hdisj a (Finset.mem_insert_self a s) j
            (Finset.mem_insert_of_mem hjJ) (fun heq => has (heq.symm ▸ hjJ))
        exact Prelim.BlockSieve.disjoint_mem_false hdisjaj hpa hjB
      have rec1 : uv.1 = (uv.1 ∪ uv.2) ∩ B a := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inl hp, huB hp⟩
        · rintro ⟨hp | hp, hpa⟩
          · exact hp
          · exact False.elim (Prelim.BlockSieve.disjoint_mem_false hvD hp hpa)
      have rec1' : uv'.1 = (uv'.1 ∪ uv'.2) ∩ B a := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inl hp, huB' hp⟩
        · rintro ⟨hp | hp, hpa⟩
          · exact hp
          · exact False.elim (Prelim.BlockSieve.disjoint_mem_false hvD' hp hpa)
      have rec2 : uv.2 = (uv.1 ∪ uv.2) \ B a := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inr hp, fun h => Prelim.BlockSieve.disjoint_mem_false hvD hp h⟩
        · rintro ⟨hp | hp, hnb⟩
          · exact absurd (huB hp) hnb
          · exact hp
      have rec2' : uv'.2 = (uv'.1 ∪ uv'.2) \ B a := by
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
    have himg : (∑ d ∈ ((((B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
            (Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e)).image
            (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)),
          (-1 : ℝ) ^ d.card * ∏ p ∈ d, g p)
        = ∑ uv ∈ ((B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
          (Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e),
          (-1 : ℝ) ^ (uv.1 ∪ uv.2).card * ∏ p ∈ uv.1 ∪ uv.2, g p :=
      Finset.sum_image hinj
    have hdouble : (∑ uv ∈ ((B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
            (Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e),
          (-1 : ℝ) ^ (uv.1 ∪ uv.2).card * ∏ p ∈ uv.1 ∪ uv.2, g p)
        = (∑ u ∈ (B a).powerset.filter (fun u => u.card ≤ e a),
            (-1 : ℝ) ^ u.card * ∏ p ∈ u, g p)
          * (∑ v ∈ Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e,
            (-1 : ℝ) ^ v.card * ∏ p ∈ v, g p) := by
      have eprod : (∑ uv ∈ ((B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
              (Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e),
            (-1 : ℝ) ^ (uv.1 ∪ uv.2).card * ∏ p ∈ uv.1 ∪ uv.2, g p)
          = ∑ u ∈ (B a).powerset.filter (fun u => u.card ≤ e a),
            ∑ v ∈ Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e,
            (-1 : ℝ) ^ (u ∪ v).card * ∏ p ∈ u ∪ v, g p :=
        Finset.sum_product _ _ _
      have emul : (∑ u ∈ (B a).powerset.filter (fun u => u.card ≤ e a),
            (-1 : ℝ) ^ u.card * ∏ p ∈ u, g p)
          * (∑ v ∈ Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e,
            (-1 : ℝ) ^ v.card * ∏ p ∈ v, g p)
          = ∑ u ∈ (B a).powerset.filter (fun u => u.card ≤ e a),
            ∑ v ∈ Prelim.BlockSieve.SieveSupport (s.biUnion B) s B e,
            ((-1 : ℝ) ^ u.card * ∏ p ∈ u, g p) *
              ((-1 : ℝ) ^ v.card * ∏ p ∈ v, g p) :=
        Finset.sum_mul_sum _ _ _ _
      rw [eprod, emul]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have huB : u ⊆ B a :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
      have hvP : v ⊆ s.biUnion B :=
        (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hv |>.1
      have hvD : Disjoint v (B a) := by
        rw [Finset.disjoint_left]
        intro p hpv hpa
        have hPp : p ∈ s.biUnion B := hvP hpv
        rw [Finset.mem_biUnion] at hPp
        obtain ⟨j, hjJ, hjB⟩ := hPp
        have hdisjaj : Disjoint (B a) (B j) :=
          hdisj a (Finset.mem_insert_self a s) j
            (Finset.mem_insert_of_mem hjJ) (fun heq => has (heq.symm ▸ hjJ))
        exact Prelim.BlockSieve.disjoint_mem_false hdisjaj hpa hjB
      have hdisjuv : Disjoint u v :=
        Finset.disjoint_left.mpr (fun p hpu hpv =>
          Prelim.BlockSieve.disjoint_mem_false hvD hpv (huB hpu))
      rw [Finset.card_union_of_disjoint hdisjuv, pow_add,
        Finset.prod_union hdisjuv]
      ring
    rw [hdecomp, himg, hdouble, ha_side, ih', hprod]

end PrelimLemmas
end Erdos821
