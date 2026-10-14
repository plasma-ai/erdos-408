import Erdos821.P3Clean.ActionLifting
import Erdos821.P3Clean.Phases

/-! A finite permutation generates a cyclic residue-translation action. -/

noncomputable section

namespace Erdos821.P3Clean

variable {V : Type*}

abbrev TranslationCycle (e : Equiv.Perm V) := Additive (Subgroup.zpowers e)

instance translationCycleAddCommGroup (e : Equiv.Perm V) : AddCommGroup (TranslationCycle e) := by
  letI : CommGroup (Subgroup.zpowers e) := IsCyclic.commGroup
  infer_instance

def cycleAct (e : Equiv.Perm V) (r : TranslationCycle e) : V ≃ V := r.toMul.val

def cycleStep (e : Equiv.Perm V) : TranslationCycle e :=
  Additive.ofMul ⟨e, Subgroup.mem_zpowers e⟩

theorem cycleAct_add (e : Equiv.Perm V) (r d : TranslationCycle e) (v : V) :
    cycleAct e (r + d) v = cycleAct e d (cycleAct e r v) := by
  have h : r + d = d + r := add_comm _ _
  rw [h]
  rfl

theorem cycleAct_step_nsmul (e : Equiv.Perm V) (n : ℕ) :
    cycleAct e (n • cycleStep e) = e ^ n := by
  change ((Additive.toMul (n • cycleStep e)).val : Equiv.Perm V) = e ^ n
  simp [cycleStep, toMul_nsmul, Subgroup.coe_pow]

theorem cycleAct_step_zsmul (e : Equiv.Perm V) (n : ℤ) :
    cycleAct e (n • cycleStep e) = e ^ n := by
  change ((Additive.toMul (n • cycleStep e)).val : Equiv.Perm V) = e ^ n
  simp [cycleStep, toMul_zsmul, Subgroup.coe_zpow]

theorem weight_perm_zpow (e : Equiv.Perm V) (weight : V → ℝ)
    (h : ∀ v, weight (e v) = weight v) (n : ℤ) (v : V) : weight ((e ^ n) v) = weight v := by
  have hp (n : ℕ) (v : V) : weight ((e ^ n) v) = weight v := by
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ']
      exact (h _).trans hn
  have hi (v : V) : weight (e.symm v) = weight v := by
    simpa only [Equiv.apply_symm_apply] using (h (e.symm v)).symm
  have hpi (n : ℕ) (v : V) : weight ((e.symm ^ n) v) = weight v := by
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ']
      exact (hi _).trans hn
  cases n with
  | ofNat n => change weight ((e ^ n) v) = weight v; exact hp n v
  | negSucc n => simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using hpi (n + 1) v

theorem cycleAct_preserves_weight (e : Equiv.Perm V) (weight : V → ℝ)
    (h : ∀ v, weight (e v) = weight v) (r : TranslationCycle e) (v : V) :
    weight (cycleAct e r v) = weight v := by
  obtain ⟨n, hn⟩ := r.toMul.property
  change weight (r.toMul.val v) = weight v
  rw [← hn]
  exact weight_perm_zpow e weight h n v


end Erdos821.P3Clean
