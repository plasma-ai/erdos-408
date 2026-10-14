module

public import Erdos408.Hypotheses
public import Erdos821.Blueprint.Ideal

/-!
# Encoding the active groups as upstream data

`GraphTransference` takes its groups as `P : ι → Finset ℕ` with a `Finset` of
big groups, and its constants as reals. Upstream (totient-fibers-lean4, the
modules `Erdos821.*`) takes them as a `PrimeGroups` indexed by `Fin count`
with a Boolean flag, and a `FixedData`. For groups indexed by `Fin n`:

* `fixedData` puts the exponents `.27 < .36 < .39 < .46` of PD (6.1), one final
  slot, damping `q₀`, and the group constants, with `C₀` and `v₊` raised to `1`
  where upstream needs them positive;
* `primeGroups` flags the big groups;
* `admissible` and `intervalBigGroups_primeGroups` are upstream's
  `Admissible` and `intervalBigGroups` from `GraphTransference`'s premises.
-/

@[expose] public section

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph

/-- The fixed data of PD (6.1): exponents `.27, .36, .39, .46`, one final slot,
damping `q₀`, and the group constants. Upstream needs `C₀, v₊ > 0`, so they are
raised to `1`, which only weakens the admissibility conditions. -/
noncomputable abbrev fixedData (q₀ c₀ C₀ vlo vhi : ℝ) (hq₀ : 0 < q₀) (hq₁ : q₀ < 1)
    (hc₀ : 0 < c₀) (hvlo : 0 < vlo) : FixedData where
  a := 0.27
  b := 0.36
  c := 0.39
  d := 0.46
  c₀ := c₀
  C₀ := max C₀ 1
  vMin := vlo
  vMax := max vhi 1
  q := q₀
  ell := 1
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  cd := by norm_num
  d_lt := by norm_num
  c₀_pos := hc₀
  C₀_pos := lt_max_of_lt_right one_pos
  vMin_pos := hvlo
  vMax_pos := lt_max_of_lt_right one_pos
  q_pos := hq₀
  q_lt := hq₁
  ell_pos := le_rfl

/-- The groups `P : Fin n → Finset ℕ` with the big ones flagged. -/
abbrev primeGroups {n : ℕ} (P : Fin n → Finset ℕ) (big : Finset (Fin n))
    (hP : ∀ g p, p ∈ P g → p.Prime) (hd : ∀ g h, g ≠ h → Disjoint (P g) (P h)) :
    PrimeGroups where
  count := n
  primes := P
  big g := decide (g ∈ big)
  prime := hP
  disjoint := hd

/-- The members of `primesIcc a b` are primes in `[a, b]`. -/
lemma mem_primesIcc {a b : ℝ} {p : ℕ} (hp : p ∈ primesIcc a b) :
    p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b := by
  rw [primesIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨hp.2, Nat.ceil_le.mp hp.1.1, (Nat.le_floor_iff' hp.2.ne_zero).mp hp.1.2⟩

/-- `p ∈ primesIcc a b` exactly when `p` is a prime in `[a, b]`. -/
lemma mem_primesIcc_iff {a b : ℝ} {p : ℕ} :
    p ∈ primesIcc a b ↔ p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b := by
  refine ⟨mem_primesIcc, fun ⟨hp, ha, hb⟩ => ?_⟩
  rw [primesIcc, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.ceil_le.mpr ha, (Nat.le_floor_iff' hp.ne_zero).mpr hb⟩, hp⟩

section

variable {n : ℕ} {P : Fin n → Finset ℕ} {big : Finset (Fin n)}
  {hP : ∀ g p, p ∈ P g → p.Prime} {hd : ∀ g h, g ≠ h → Disjoint (P g) (P h)}

/-- The small groups are those outside `big`. -/
lemma smallGroups_primeGroups :
    (primeGroups P big hP hd).smallGroups = Finset.univ \ big := by
  ext g
  change g ∈ Finset.univ.filter (fun g : Fin n => decide (g ∈ big) = false) ↔ _
  simp

/-- The big groups are those of `big`. -/
lemma bigGroups_primeGroups : (primeGroups P big hP hd).bigGroups = big := by
  ext g
  change g ∈ Finset.univ.filter (fun g : Fin n => decide (g ∈ big) = true) ↔ _
  simp

/-- Upstream's group mass is the harmonic mass. -/
lemma V_primeGroups (g : Fin n) : (primeGroups P big hP hd).V g = harmonicMass (P g) := by
  simp [PrimeGroups.V, harmonicMass]

/-- The big groups of `primeGroups` are intervals of primes when each `P g`,
`g ∈ big`, is a `primesIcc`. -/
lemma intervalBigGroups_primeGroups (h : ∀ g ∈ big, ∃ y z : ℝ, P g = primesIcc y z) :
    intervalBigGroups (primeGroups P big hP hd) := by
  rintro ⟨g, hg⟩
  have hg' : g ∈ big := by simpa [primeGroups] using hg
  obtain ⟨y, z, hyz⟩ := h g hg'
  exact ⟨y, z, fun p => by simp only [hyz]; exact mem_primesIcc_iff⟩

/-- `GraphTransference`'s premises on the groups make `primeGroups` admissible
for `fixedData`. -/
lemma admissible {q₀ c₀ C₀ vlo vhi : ℝ} {hq₀ : 0 < q₀} {hq₁ : q₀ < 1} {hc₀ : 0 < c₀}
    {hvlo : 0 < vlo} {x : ℝ} (hT : 0 ≤ Real.log (Real.log x))
    (hs₁ : c₀ * Real.log (Real.log x) ≤ (Finset.univ \ big).card)
    (hs₂ : ((Finset.univ \ big).card : ℝ) ≤ C₀ * Real.log (Real.log x))
    (hb₁ : c₀ * Real.log (Real.log x) ≤ big.card)
    (hb₂ : (big.card : ℝ) ≤ C₀ * Real.log (Real.log x))
    (hV : ∀ g, vlo ≤ harmonicMass (P g) ∧ harmonicMass (P g) ≤ vhi)
    (hsmall : ∀ g ∉ big, P g ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
      (Real.exp (Real.log x ^ (0.36 : ℝ))))
    (hbig : ∀ g ∈ big, P g ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
      (Real.exp (Real.log x ^ (0.46 : ℝ)))) :
    (primeGroups P big hP hd).Admissible (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) x := by
  have hC : C₀ * Real.log (Real.log x) ≤ max C₀ 1 * Real.log (Real.log x) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hT
  refine ⟨?_, ?_, ?_, ?_, fun g => ?_, fun g p hp => ?_⟩
  · rw [smallGroups_primeGroups]; exact hs₁
  · rw [smallGroups_primeGroups]; exact hs₂.trans hC
  · rw [bigGroups_primeGroups]; exact hb₁
  · rw [bigGroups_primeGroups]; exact hb₂.trans hC
  · change vlo ≤ (primeGroups P big hP hd).V g ∧ (primeGroups P big hP hd).V g ≤ max vhi 1
    rw [V_primeGroups]
    exact ⟨(hV g).1, (hV g).2.trans (le_max_left _ _)⟩
  · change p ∈ P g at hp
    change if decide (g ∈ big) = true then _ else _
    by_cases hg : g ∈ big
    · rw [ite_eq_left (decide_eq_true hg)]
      exact (mem_primesIcc (hbig g hg hp)).2
    · rw [ite_eq_right (by simpa using hg)]
      exact (mem_primesIcc (hsmall g hg hp)).2

end

end Erdos408.Graph
