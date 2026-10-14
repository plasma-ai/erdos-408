import Erdos821.S34.Probability

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

noncomputable section

def primeTupleFiber (S : Finset ℕ) (j n : ℕ) : Finset (Fin j → ↥S) :=
  Finset.univ.filter fun z => (∏ i, (z i).val) = n

/-- Repetitions of primes are allowed; the number of ordered representations
of a product with j selected primes is at most j factorial. -/
theorem primeTupleFiber_card_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (j n : ℕ) :
    (primeTupleFiber S j n).card ≤ Nat.factorial j := by
  by_cases hne : (primeTupleFiber S j n).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    let Φ : (Fin j → ↥S) → List ℕ := fun z => List.ofFn (fun i => (z i).val)
    have hΦ : Function.Injective Φ := by
      intro z w h
      have hv := List.ofFn_injective h
      funext i
      apply Subtype.ext
      exact congrFun hv i
    have hp (z : Fin j → ↥S) : ∀ p ∈ Φ z, p.Prime := by
      intro p hp
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
      subst p
      exact hS _ (z i).property
    have hzprod : (Φ z₀).prod = n := by
      rw [List.prod_ofFn]
      exact (Finset.mem_filter.mp hz₀).2
    have hsub : (primeTupleFiber S j n).image Φ ⊆ (Φ z₀).permutations.toFinset := by
      intro l hl
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hl
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      have hz' : (Φ z).prod = n := by
        rw [List.prod_ofFn]
        exact (Finset.mem_filter.mp hz).2
      exact (Nat.primeFactorsList_unique hz' (hp z)).trans
        (Nat.primeFactorsList_unique hzprod (hp z₀)).symm
    calc
      _ = ((primeTupleFiber S j n).image Φ).card := (Finset.card_image_of_injective _ hΦ).symm
      _ ≤ (Φ z₀).permutations.toFinset.card := Finset.card_le_card hsub
      _ ≤ (Φ z₀).permutations.length := List.toFinset_card_le _
      _ = Nat.factorial j := by rw [List.length_permutations]; simp [Φ]
  · have h := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [h]
    simp

theorem count_nat_ofFn (j : ℕ) (f : Fin j → ℕ) (p : ℕ) :
    List.count p (List.ofFn f) = ∑ i, if f i = p then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.count_cons, ih]
    by_cases h : f 0 = p
    · simp [h, Nat.add_comm]
    · simp [h, Nat.add_comm]

theorem tuple_factorization (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z : S34.Core.Tuple G k) :
    (S34.Core.product G k z).factorization =
      ∑ g, ∑ i, Finsupp.single (z g i).val 1 := by
  have hrow (g : Fin G.size) : (∏ i, (z g i).val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (G.prime g _ (z g i).property).ne_zero
  unfold S34.Core.product
  rw [Nat.factorization_prod (fun g _ => hrow g)]
  apply Finset.sum_congr rfl
  intro g _
  rw [Nat.factorization_prod (fun i _ => (G.prime g _ (z g i).property).ne_zero)]
  apply Finset.sum_congr rfl
  intro i _
  exact (G.prime g _ (z g i).property).factorization

theorem group_count_factorization (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z : S34.Core.Tuple G k) (g : Fin G.size) (p : ℕ) (hp : p ∈ G.primes g) :
    (S34.Core.product G k z).factorization p =
      List.count p (List.ofFn (fun i => (z g i).val)) := by
  rw [tuple_factorization, count_nat_ofFn]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_single g
  · intro h _ hne
    apply Finset.sum_eq_zero
    intro i _
    have hneq : (z h i).val ≠ p := by
      intro heq
      have hmem : p ∈ G.primes h := heq ▸ (z h i).property
      exact Finset.disjoint_left.mp (G.disjoint h g hne) hmem hp
    simp [hneq]
  · intro hcontra
    exact False.elim (hcontra (Finset.mem_univ g))

theorem group_row_perm (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z w : S34.Core.Tuple G k) (g : Fin G.size)
    (hprod : S34.Core.product G k z = S34.Core.product G k w) :
    (List.ofFn (fun i => (z g i).val)).Perm (List.ofFn (fun i => (w g i).val)) := by
  apply List.perm_iff_count.mpr
  intro p
  by_cases hp : p ∈ G.primes g
  · rw [← group_count_factorization G k z g p hp,
      ← group_count_factorization G k w g p hp, hprod]
  · have hmem (v : S34.Core.Tuple G k) : p ∉ List.ofFn (fun i => (v g i).val) := by
      intro h
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      apply hp
      rw [← hi]
      exact (v g i).property
    rw [List.count_eq_zero.mpr (hmem z), List.count_eq_zero.mpr (hmem w)]

def tupleFiber (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) :
    Finset (S34.Core.Tuple G k) := Finset.univ.filter fun z => S34.Core.product G k z = n

/-- Unique factorization and disjoint prime groups keep the representation
cost multiplicative in the individual slot counts. -/
theorem tupleFiber_card_le (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) :
    (tupleFiber G k n).card ≤ ∏ g, Nat.factorial (k g) := by
  by_cases hne : (tupleFiber G k n).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    let target : Type := ∀ g : Fin G.size,
      ↥((List.ofFn (fun i => (z₀ g i).val)).permutations.toFinset)
    let encode : ↥(tupleFiber G k n) → target := fun z g =>
      ⟨List.ofFn (fun i => (z.val g i).val), by
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        apply group_row_perm G k z.val z₀ g
        exact (Finset.mem_filter.mp z.property).2.trans (Finset.mem_filter.mp hz₀).2.symm⟩
    have hinj : Function.Injective encode := by
      intro z w h
      apply Subtype.ext
      funext g i
      apply Subtype.ext
      have hg := congrArg Subtype.val (congrFun h g)
      exact congrFun (List.ofFn_injective hg) i
    have hc := Fintype.card_le_of_injective encode hinj
    calc
      _ = Fintype.card ↥(tupleFiber G k n) := by simp
      _ ≤ Fintype.card target := hc
      _ = ∏ g, (List.ofFn (fun i => (z₀ g i).val)).permutations.toFinset.card := by simp [target]
      _ ≤ ∏ g, Nat.factorial (k g) := by
        gcongr with g
        calc
          _ ≤ (List.ofFn (fun i => (z₀ g i).val)).permutations.length := List.toFinset_card_le _
          _ = _ := by rw [List.length_permutations]; simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end
end Erdos821.S34Core
