import Erdos821.Blueprint.Graph
import Erdos821.S2.RankCount

/-! Exact P3 blueprint exports for the equality-rank combinatorics. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.Graph

theorem distinct_birth_expansion_proof : Erdos821.Blueprint.Graph.distinct_birth_expansion_statement := by
  intro a performed value
  let U : Finset (Finset (Finset (Fin a))) := Finset.univ.powerset.powerset
  have hfilter : U.filter Erdos821.S2.BirthCollection = U.filter BirthCollection := by
    ext π
    simp only [Finset.mem_filter, BirthCollection, Erdos821.S2.BirthCollection]
  calc
    _ = ∑ π ∈ U.filter Erdos821.S2.BirthCollection,
        if Erdos821.S2.birthEvent performed value π then Erdos821.S2.birthMobius π else 0 :=
      Erdos821.S2.distinct_birth_expansion a performed value
    _ = _ := by
      apply Finset.sum_congr hfilter
      intro π _
      have he : Erdos821.S2.birthEvent performed value π ↔ birthEvent performed value π := Iff.rfl
      by_cases hp : birthEvent performed value π
      · simp only [if_pos hp, if_pos (he.mpr hp), birthMobius, Erdos821.S2.birthMobius]
      · simp only [if_neg hp, if_neg (fun hs => hp (he.mp hs))]

example : Erdos821.Blueprint.Graph.distinct_birth_expansion_statement := @distinct_birth_expansion_proof

theorem birth_support_le_proof : type_of% @birth_support_le := by
  intro a π hπ
  have hp : Erdos821.S2.BirthCollection π := by
    simpa only [BirthCollection, Erdos821.S2.BirthCollection] using hπ
  simpa only [birthRank, Erdos821.S2.birthRank] using Erdos821.S2.birth_support_le π hp

example : type_of% @birth_support_le := @birth_support_le_proof

theorem rank_coefficient_count_proof : Erdos821.Blueprint.Graph.rank_coefficient_count_statement := by
  intro a r
  let U : Finset (Finset (Finset (Fin a))) := Finset.univ.powerset.powerset
  have hfilter :
      U.filter (fun π => BirthCollection π ∧ birthRank π = r) =
      U.filter (fun π => Erdos821.S2.BirthCollection π ∧ Erdos821.S2.birthRank π = r) := by
    ext π
    constructor
    · intro hp
      obtain ⟨hU, hc, hr⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      exact ⟨hU, hc, hr⟩
    · intro hp
      obtain ⟨hU, hc, hr⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      exact ⟨hU, hc, hr⟩
  rw [hfilter]
  simpa only [birthMobius, Erdos821.S2.birthMobius] using Erdos821.S2.rank_coefficient_count a r

example : Erdos821.Blueprint.Graph.rank_coefficient_count_statement := @rank_coefficient_count_proof

end Erdos821.Blueprint.Graph
