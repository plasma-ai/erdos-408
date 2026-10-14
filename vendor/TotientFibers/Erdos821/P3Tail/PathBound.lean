import Mathlib

/-! Chronological elimination for finite sets of alternating state paths. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Tail

/-- One elimination step: fibre bounds and a kernel row bound control a finite sum. -/
theorem fiber_step {α β : Type*} [DecidableEq α] (w K : α → ℝ) (C M ws : ℝ)
    (hK : ∀ t, 0 ≤ K t) (hw : ∀ t, 0 ≤ w t) (hM : 0 ≤ M)
    (hsum : Summable (fun t => K t * w t)) (hrow : ∑' t, K t * w t ≤ C * ws)
    (S : Finset β) (h : β → α) (R : β → ℝ)
    (hfib : ∀ t, ∑ x ∈ S.filter (fun x => h x = t), R x ≤ M * w t) :
    ∑ x ∈ S, K (h x) * R x ≤ M * (C * ws) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := h) (t := S.image h)
    (fun x hx => Finset.mem_image_of_mem h hx)]
  calc ∑ t ∈ S.image h, ∑ x ∈ S.filter (fun x => h x = t), K (h x) * R x
      = ∑ t ∈ S.image h, K t * ∑ x ∈ S.filter (fun x => h x = t), R x := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.1 hx).2]
    _ ≤ ∑ t ∈ S.image h, K t * (M * w t) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hfib t) (hK t)
    _ = M * ∑ t ∈ S.image h, K t * w t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
    _ ≤ M * ∑' t, K t * w t :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ (fun t _ => mul_nonneg (hK t) (hw t))) hM
    _ ≤ M * (C * ws) := mul_le_mul_of_nonneg_left hrow hM

/-- Ghost kernels on `(before i, after i)`, edge kernels on `(after i, before (i+1))`,
and the weight at the final state. -/
def pathWeight {α : Type*} (w : α → ℝ) (n : ℕ) (G : Fin (n + 1) → α → α → ℝ)
    (E : Fin n → α → α → ℝ) (z : Fin (n + 1) → α × α) : ℝ :=
  (∏ i, G i (z i).1 (z i).2) * (∏ i : Fin n, E i (z i.castSucc).2 (z i.succ).1) *
    w (z (Fin.last n)).2

theorem pathWeight_succ {α : Type*} (w : α → ℝ) (n : ℕ) (G : Fin (n + 2) → α → α → ℝ)
    (E : Fin (n + 1) → α → α → ℝ) (z : Fin (n + 2) → α × α) :
    pathWeight w (n + 1) G E z =
      G 0 (z 0).1 (z 0).2 * (E 0 (z 0).2 (z 1).1 *
        pathWeight w n (fun i => G i.succ) (fun i => E i.succ) (Fin.tail z)) := by
  unfold pathWeight
  have hc : ∀ i : Fin n, (i.succ.castSucc : Fin (n + 2)) = i.castSucc.succ := fun i => Fin.ext rfl
  rw [Fin.prod_univ_succ (f := fun i : Fin (n + 2) => G i (z i).1 (z i).2),
    Fin.prod_univ_succ (f := fun i : Fin (n + 1) => E i (z i.castSucc).2 (z i.succ).1)]
  simp only [Fin.tail, Fin.succ_last, Fin.castSucc_zero, Fin.succ_zero_eq_one, hc]
  ring

theorem path_bound {α : Type*} (w : α → ℝ) (hw : ∀ t, 0 ≤ w t) (CG CE : ℝ)
    (hCG : 0 ≤ CG) (hCE : 0 ≤ CE) :
    ∀ (n : ℕ) (G : Fin (n + 1) → α → α → ℝ) (E : Fin n → α → α → ℝ),
      (∀ i s t, 0 ≤ G i s t) → (∀ i s t, 0 ≤ E i s t) →
      (∀ i s, Summable (fun t => G i s t * w t) ∧ ∑' t, G i s t * w t ≤ CG * w s) →
      (∀ i s, Summable (fun t => E i s t * w t) ∧ ∑' t, E i s t * w t ≤ CE * w s) →
      ∀ (S : Finset (Fin (n + 1) → α × α)) (s : α), (∀ z ∈ S, (z 0).1 = s) →
        ∑ z ∈ S, pathWeight w n G E z ≤ CG ^ (n + 1) * CE ^ n * w s := by
  classical
  intro n
  induction n with
  | zero =>
      intro G E hG _ hGr _ S s hS
      have hrw : ∑ z ∈ S, pathWeight w 0 G E z =
          ∑ z ∈ S, G 0 s ((fun z : Fin 1 → α × α => (z 0).2) z) * w (z 0).2 := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [pathWeight, hS z hz, Fin.last]
      rw [hrw]
      have := fiber_step w (G 0 s) CG 1 (w s) (hG 0 s) hw zero_le_one (hGr 0 s).1 (hGr 0 s).2
        S (fun z : Fin 1 → α × α => (z 0).2) (fun z => w (z 0).2) (by
          intro t
          have hc : (S.filter (fun z : Fin 1 → α × α => (z 0).2 = t)).card ≤ 1 := by
            apply Finset.card_le_one.2
            intro a ha b hb
            rw [Finset.mem_filter] at ha hb
            funext i
            have hi : i = 0 := Subsingleton.elim _ _
            subst hi
            exact Prod.ext ((hS a ha.1).trans (hS b hb.1).symm) (ha.2.trans hb.2.symm)
          calc ∑ z ∈ S.filter (fun z : Fin 1 → α × α => (z 0).2 = t), w (z 0).2
              = ∑ z ∈ S.filter (fun z : Fin 1 → α × α => (z 0).2 = t), w t := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [(Finset.mem_filter.1 hz).2]
            _ = (S.filter (fun z : Fin 1 → α × α => (z 0).2 = t)).card * w t := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 1 * w t := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hw t))
      simpa using this
  | succ n ih =>
      intro G E hG hE hGr hEr S s hS
      let G' : Fin (n + 1) → α → α → ℝ := fun i => G i.succ
      let E' : Fin n → α → α → ℝ := fun i => E i.succ
      have IH := ih G' E' (fun i => hG i.succ) (fun i => hE i.succ)
        (fun i => hGr i.succ) (fun i => hEr i.succ)
      have hK : 0 ≤ CG ^ (n + 1) * CE ^ n := by positivity
      have hrw : ∑ z ∈ S, pathWeight w (n + 1) G E z =
          ∑ z ∈ S, G 0 s ((fun z : Fin (n + 2) → α × α => (z 0).2) z) *
            (E 0 (z 0).2 (z 1).1 * pathWeight w n G' E' (Fin.tail z)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [pathWeight_succ, hS z hz]
      rw [hrw]
      have hstep := fiber_step w (G 0 s) CG (CG ^ (n + 1) * CE ^ n * CE) (w s) (hG 0 s) hw
        (mul_nonneg hK hCE) (hGr 0 s).1 (hGr 0 s).2 S
        (fun z : Fin (n + 2) → α × α => (z 0).2)
        (fun z => E 0 (z 0).2 (z 1).1 * pathWeight w n G' E' (Fin.tail z)) (by
          intro t
          let St := S.filter (fun z : Fin (n + 2) → α × α => (z 0).2 = t)
          have hrw2 : ∑ z ∈ St, E 0 (z 0).2 (z 1).1 * pathWeight w n G' E' (Fin.tail z) =
              ∑ z ∈ St, E 0 t ((fun z : Fin (n + 2) → α × α => (z 1).1) z) *
                pathWeight w n G' E' (Fin.tail z) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [(Finset.mem_filter.1 hz).2]
          change ∑ z ∈ St, _ ≤ _
          rw [hrw2]
          have h2 := fiber_step w (E 0 t) CE (CG ^ (n + 1) * CE ^ n) (w t) (hE 0 t) hw hK
            (hEr 0 t).1 (hEr 0 t).2 St (fun z : Fin (n + 2) → α × α => (z 1).1)
            (fun z => pathWeight w n G' E' (Fin.tail z)) (by
              intro u
              let Su := St.filter (fun z : Fin (n + 2) → α × α => (z 1).1 = u)
              have hinj : Set.InjOn (fun z : Fin (n + 2) → α × α => Fin.tail z) Su := by
                intro a ha b hb hab
                rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at ha hb
                have h0 : a 0 = b 0 :=
                  Prod.ext ((hS a ha.1.1).trans (hS b hb.1.1).symm) (ha.1.2.trans hb.1.2.symm)
                rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
                simp only at hab
                rw [h0, hab]
              change ∑ z ∈ Su, _ ≤ _
              rw [← Finset.sum_image (f := pathWeight w n G' E') hinj]
              apply IH
              intro y hy
              obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
              exact (Finset.mem_filter.1 hz).2)
          calc _ ≤ CG ^ (n + 1) * CE ^ n * (CE * w t) := h2
            _ = CG ^ (n + 1) * CE ^ n * CE * w t := by ring)
      calc _ ≤ CG ^ (n + 1) * CE ^ n * CE * (CG * w s) := hstep
        _ = CG ^ (n + 1 + 1) * CE ^ (n + 1) * w s := by ring


end Erdos821.P3Tail
