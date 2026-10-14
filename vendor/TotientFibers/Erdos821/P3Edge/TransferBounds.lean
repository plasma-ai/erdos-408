import Erdos821.S2.MemoryEdge
import Erdos821.Leaves

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Non-shared slots fit in `t_g = ell + changed`. -/
lemma nonshared_card_le (ν : Pattern P J F.ell m) (g : P.Group) :
    (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g i)).card
      ≤ ν.t g := by
  classical
  have hslot_inj : Function.Injective ν.slot := by
    intro a b h
    have hval : (ν.slot a).val = (ν.slot b).val := congrArg Fin.val h
    have hval2 : a.val = b.val := hval
    exact Fin.ext hval2
  have himg_card : (((Finset.univ \ ν.changed g).map
      ⟨ν.slot, hslot_inj⟩)).card = J - (ν.changed g).card := by
    rw [Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hsub : (((Finset.univ \ ν.changed g).map
      ⟨ν.slot, hslot_inj⟩)) ⊆
      Finset.univ.filter (fun i : Fin (J + F.ell) => ν.shared g i) := by
    intro i hi
    simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, rfl, hj⟩
  have hcard := Finset.card_le_card hsub
  rw [himg_card] at hcard
  have htot : (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g i)).card +
      (Finset.univ.filter (fun i : Fin (J + F.ell) => ν.shared g i)).card
      = J + F.ell := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (J + F.ell)))) (fun i => ν.shared g i)
    rw [Finset.card_univ, Fintype.card_fin] at h
    linarith
  have htb : (ν.changed g).card ≤ m := ν.bound g
  unfold Pattern.t
  omega

lemma prom_card_le (ν : Pattern P J F.ell m) (g : P.BigGroup)
    (B : Finset (Fin (J + F.ell))) (hB : ∀ i ∈ B, ¬ ν.shared g.val i) :
    B.card ≤ F.ell + m := by
  have h1 : B.card ≤ (Finset.univ.filter
    (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hB i hi
  have h2 := nonshared_card_le ν g.val
  have h3 : (ν.changed g.val).card ≤ m := ν.bound g.val
  unfold Pattern.t at h2
  omega

/-- Transfer subset pairs live in a `J`-independent powerset. -/
lemma transfer_pairs_card_le (ν : Pattern P J F.ell m) (g : P.BigGroup) :
    ((Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset ×ˢ
      (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset).card
      ≤ 4 ^ (F.ell + m) := by
  have htg : (Finset.univ.filter
      (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).card ≤ F.ell + m := by
    have h2 := nonshared_card_le ν g.val
    have h3 : (ν.changed g.val).card ≤ m := ν.bound g.val
    unfold Pattern.t at h2
    omega
  calc ((Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset ×ˢ
        (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset).card
      = 2 ^ (Finset.univ.filter _).card * 2 ^ (Finset.univ.filter _).card := by
        rw [Finset.card_product, Finset.card_powerset]
    _ ≤ 2 ^ (F.ell + m) * 2 ^ (F.ell + m) :=
        Nat.mul_le_mul (pow_le_pow_right₀ (by norm_num) htg)
          (pow_le_pow_right₀ (by norm_num) htg)
    _ = 4 ^ (F.ell + m) := by
        calc 2 ^ (F.ell+m) * 2 ^ (F.ell+m)
            = (2 * 2) ^ (F.ell+m) := (mul_pow (2:Nat) 2 (F.ell+m)).symm
          _ = 4 ^ (F.ell+m) := by
              have h44 : (2:Nat) * 2 = 4 := by norm_num
              rw [h44]

/-- Promotion coefficients are bounded via `vMin`, uniformly for `a ≤ ell+m`. -/
lemma Vinv_pow_le (hv : 0 < F.vMin) (V : ℝ) (hV : F.vMin ≤ V)
    (a : ℕ) (ha : a ≤ F.ell + m) :
    V ^ (-(a : ℤ)) ≤ max 1 (F.vMin⁻¹ ^ (F.ell + m)) :=
  Erdos821.GraphLemmas.vinv_bound F.vMin V hv hV a (F.ell + m) ha

/-- Column reversal factor per group, uniformly for `a,b ≤ ell+m`. -/
lemma V_pow_sub_le (hv : 0 < F.vMin) (V : ℝ) (hVlo : F.vMin ≤ V) (hVhi : V ≤ F.vMax)
    (a b : ℕ) (ha : a ≤ F.ell + m) (hb : b ≤ F.ell + m) :
    V ^ ((b : ℤ) - (a : ℤ)) ≤ max 1 (max (F.vMax ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m))) := by
  have hVpos : 0 < V := lt_of_lt_of_le hv hVlo
  by_cases h : a ≤ b
  · have he : ((b:ℤ) - (a:ℤ)) = (((b - a : ℕ)):ℤ) := by omega
    rw [he, zpow_natCast]
    by_cases hV1 : 1 ≤ V
    · have h1max : 1 ≤ F.vMax := le_trans hV1 hVhi
      calc V ^ (b - a) ≤ F.vMax ^ (b - a) :=
              pow_le_pow_left₀ hVpos.le hVhi _
        _ ≤ F.vMax ^ (F.ell + m) :=
              pow_le_pow_right₀ h1max (Nat.le_trans (Nat.sub_le b a) hb)
        _ ≤ max 1 (max (F.vMax ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m))) :=
              le_max_of_le_right (le_max_left _ _)
    · have hVlt : V < 1 := lt_of_not_ge hV1
      calc V ^ (b - a) ≤ 1 := pow_le_one₀ hVpos.le hVlt.le
        _ ≤ max 1 (max (F.vMax ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m))) :=
              le_max_left _ _
  · push Not at h
    have hba : b < a := by exact_mod_cast h
    have he : ((b:ℤ) - (a:ℤ)) = -(((a - b : ℕ)):ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, ← inv_pow]
    have hVinv : V⁻¹ ≤ F.vMin⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hv hVlo
    have hVinv_pos : 0 < V⁻¹ := inv_pos.mpr hVpos
    have hsub : a - b ≤ F.ell + m := Nat.le_trans (Nat.sub_le a b) ha
    by_cases h1 : 1 ≤ V⁻¹
    · have h1max : 1 ≤ F.vMin⁻¹ := le_trans h1 hVinv
      calc (V⁻¹) ^ (a - b) ≤ (F.vMin⁻¹) ^ (a - b) :=
              pow_le_pow_left₀ hVinv_pos.le hVinv _
        _ ≤ (F.vMin⁻¹) ^ (F.ell + m) := pow_le_pow_right₀ h1max hsub
        _ ≤ max 1 (max (F.vMax ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m))) :=
              le_max_of_le_right (le_max_right _ _)
    · have hlt : V⁻¹ < 1 := lt_of_not_ge h1
      calc (V⁻¹) ^ (a - b) ≤ 1 := pow_le_one₀ hVinv_pos.le hlt.le
        _ ≤ max 1 (max (F.vMax ^ (F.ell + m)) ((F.vMin⁻¹) ^ (F.ell + m))) :=
              le_max_left _ _

end Erdos821.P3Edge
