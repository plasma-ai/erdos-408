import Erdos821.Blueprint.Ideal

/-! Both models use the same group indices and prime sets. P5 needs this bridge. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint.Analytic

abbrev Geometry.graph (F : Geometry) : Graph.FixedData where
  a := F.a
  b := F.b
  c := F.c
  d := F.d
  c₀ := F.c₀
  C₀ := F.C₀
  vMin := F.vmin
  vMax := F.vmax
  q := F.q
  ell := F.ell
  a_pos := F.ordered.1
  ab := F.ordered.2.1
  bc := F.ordered.2.2.1
  cd := F.ordered.2.2.2.1
  d_lt := by convert F.ordered.2.2.2.2 using 1 <;> norm_num
  c₀_pos := F.positive.1
  C₀_pos := F.positive.2.1
  vMin_pos := F.positive.2.2.1
  vMax_pos := lt_of_lt_of_le F.positive.2.2.1 F.positive.2.2.2
  q_pos := F.damping.1
  q_lt := F.damping.2
  ell_pos := F.marks

abbrev PrimeGroups.graph (P : PrimeGroups) : Graph.PrimeGroups where
  count := P.size
  primes := P.primes
  big := fun g => decide (g ∉ P.small)
  prime := P.prime
  disjoint := P.disjoint

@[simp] theorem graph_small (P : PrimeGroups) : P.graph.smallGroups = P.small := by
  ext g
  simp [Graph.PrimeGroups.smallGroups, PrimeGroups.graph, Finset.mem_filter]

@[simp] theorem graph_big (P : PrimeGroups) : P.graph.bigGroups = P.big := by
  ext g
  simp [Graph.PrimeGroups.bigGroups, PrimeGroups.graph, PrimeGroups.big, Finset.mem_filter]

@[simp] theorem graph_mass (P : PrimeGroups) (g : Fin P.size) : P.graph.V g = mass P g := by
  simp [Graph.PrimeGroups.V, PrimeGroups.graph, mass, one_div]

/-- P5's adapter uses no pending graph theorem. -/
theorem graph_admissible (F : Geometry) (x : ℝ) (P : PrimeGroups)
    (h : Admissible F x P) : P.graph.Admissible F.graph x := by
  rcases h with ⟨hs, hb, hv, hp, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Geometry.graph, Graph.T, Graph.L, T, L] using hs.1
  · simpa [Geometry.graph, Graph.T, Graph.L, T, L] using hs.2
  · simpa [Geometry.graph, Graph.T, Graph.L, T, L] using hb.1
  · simpa [Geometry.graph, Graph.T, Graph.L, T, L] using hb.2
  · intro g
    change F.vmin ≤ P.graph.V g ∧ P.graph.V g ≤ F.vmax
    rw [graph_mass]
    exact hv g
  · intro g p hpg
    have h := hp g p hpg
    dsimp [PrimeGroups.graph, Geometry.graph, Graph.L, L] at h ⊢
    split_ifs at h ⊢ <;> simp_all

end Erdos821.Blueprint.Analytic
