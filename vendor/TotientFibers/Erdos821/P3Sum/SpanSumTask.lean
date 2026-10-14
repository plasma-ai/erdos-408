import Erdos821.S2.SpanSumTask
import Erdos821.Leaves.OrphanExp

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Sum

/-- Replace an optional distinguished endpoint by a canonical finite endpoint,
provided the duplicate optional endpoint contributes zero. -/
theorem option_sum_recode {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : Option α → ℝ) (hz : f (some a) = 0) :
    (∑ x : Option α, f x) = ∑ x : α, f (if x = a then none else some x) := by
  classical
  have hleft :
      (∑ x ∈ (Finset.univ : Finset α).erase a, f (some x)) + f (some a) =
        ∑ x : α, f (some x) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ a)
  have hright :
      (∑ x : α, f (if x = a then none else some x)) =
        (∑ x ∈ (Finset.univ : Finset α).erase a, f (some x)) + f none := by
    calc
      _ = (∑ x ∈ (Finset.univ : Finset α).erase a,
          f (if x = a then none else some x)) + f (if a = a then none else some a) :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ a)).symm
      _ = _ := by
        congr 1
        · apply Finset.sum_congr rfl
          intro x hx
          simp [(Finset.mem_erase.mp hx).1]
        · simp
  rw [Fintype.sum_option]
  calc
    f none + (∑ x : α, f (some x)) =
        f none + ((∑ x ∈ (Finset.univ : Finset α).erase a, f (some x)) + f (some a)) := by
      rw [← hleft]
    _ = (∑ x ∈ (Finset.univ : Finset α).erase a, f (some x)) + f none := by
      rw [hz]
      ring
    _ = ∑ x : α, f (if x = a then none else some x) := hright.symm

/-- Congruent endpoint offsets are exactly the zero difference used by a span. -/
theorem intCast_sub_eq_zero_iff {p : ℕ} (u v : ℤ) :
    ((u - v : ℤ) : ZMod p) = 0 ↔ (u : ZMod p) = (v : ZMod p) := by
  rw [Int.cast_sub, sub_eq_zero]

/-- Split a nonactive interval at the first and last active visits. -/
theorem span_interval_product_split {n : ℕ} (birth stop a z : Fin n)
    (active : Finset (Fin n)) (f : Fin n → ℝ)
    (hba : birth ≤ a) (haz : a ≤ z) (hze : z ≤ stop)
    (ha : a ∈ active) (hz : z ∈ active)
    (hfirst : ∀ i ∈ active, a ≤ i) (hlast : ∀ i ∈ active, i ≤ z) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin n => birth < i ∧ i < stop ∧ i ∉ active), f i) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => birth < i ∧ i < a), f i) *
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => a < i ∧ i < z ∧ i ∉ active), f i) *
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => z < i ∧ i < stop), f i) := by
  classical
  let pre := Finset.univ.filter (fun i : Fin n => birth < i ∧ i < a)
  let mid := Finset.univ.filter (fun i : Fin n => a < i ∧ i < z ∧ i ∉ active)
  let post := Finset.univ.filter (fun i : Fin n => z < i ∧ i < stop)
  let whole := Finset.univ.filter (fun i : Fin n => birth < i ∧ i < stop ∧ i ∉ active)
  have hcover : whole = pre ∪ mid ∪ post := by
    ext i
    simp only [whole, pre, mid, post, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · rintro ⟨hbi, his, hnot⟩
      by_cases hleft : i < a
      · exact Or.inl (Or.inl ⟨hbi, hleft⟩)
      · have hia : a ≤ i := le_of_not_gt hleft
        have hneA : i ≠ a := by
          intro he
          subst i
          exact hnot ha
        have hait : a < i := lt_of_le_of_ne hia (Ne.symm hneA)
        by_cases hright : z < i
        · exact Or.inr ⟨hright, his⟩
        · have hiz : i ≤ z := le_of_not_gt hright
          have hneZ : i ≠ z := by
            intro he
            subst i
            exact hnot hz
          have hitz : i < z := lt_of_le_of_ne hiz hneZ
          exact Or.inl (Or.inr ⟨hait, hitz, hnot⟩)
    · intro hi
      rcases hi with hleft | hright
      · rcases hleft with hpre | hmid
        · obtain ⟨hbi, hia⟩ := hpre
          have his : i < stop := lt_of_lt_of_le hia (le_trans haz hze)
          have hnot : i ∉ active := by
            intro hi
            exact (not_lt_of_ge (hfirst i hi)) hia
          simp [whole, hbi, his, hnot]
        · obtain ⟨hai, hiz, hnot⟩ := hmid
          have hbi : birth < i := lt_of_le_of_lt hba hai
          have his : i < stop := lt_of_lt_of_le hiz hze
          simp [whole, hbi, his, hnot]
      · obtain ⟨hzi, his⟩ := hright
        have hbi : birth < i := lt_of_le_of_lt (le_trans hba haz) hzi
        have hnot : i ∉ active := by
          intro hi
          exact (not_lt_of_ge (hlast i hi)) hzi
        simp [whole, hbi, his, hnot]
  have hpre_mid : Disjoint pre mid := by
    apply Finset.disjoint_left.mpr
    intro i hipre himid
    simp only [pre, mid, Finset.mem_filter, Finset.mem_univ, true_and] at hipre himid
    omega
  have hpre_post : Disjoint pre post := by
    apply Finset.disjoint_left.mpr
    intro i hipre hipost
    simp only [pre, post, Finset.mem_filter, Finset.mem_univ, true_and] at hipre hipost
    omega
  have hmid_post : Disjoint mid post := by
    apply Finset.disjoint_left.mpr
    intro i himid hipost
    simp only [mid, post, Finset.mem_filter, Finset.mem_univ, true_and] at himid hipost
    omega
  have hunion_post : Disjoint (pre ∪ mid) post := by
    apply Finset.disjoint_left.mpr
    intro i hi hipost
    rcases Finset.mem_union.mp hi with hipre | himid
    · exact Finset.disjoint_left.mp hpre_post hipre hipost
    · exact Finset.disjoint_left.mp hmid_post himid hipost
  change (∏ i ∈ whole, f i) = (∏ i ∈ pre, f i) * (∏ i ∈ mid, f i) * (∏ i ∈ post, f i)
  rw [hcover, Finset.prod_union hunion_post, Finset.prod_union hpre_mid]

open Erdos821.Blueprint.Graph Erdos821.S2Core

/-- The absent-prime case is the orphan expansion with its constant part
collected into the baseline. -/
theorem inactive_span_sum
    (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (g : P.BigGroup) (p : P.Prime g.val)
    (hbase : baselinePrime F n p.val ≠ 0)
    (hactive : Q.activeVisits g p = ∅) :
    (∑ span : PrimeSpan n, Q.spanWeight g p span) =
      (baselinePrime F n p.val)⁻¹ *
        onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
  classical
  let η : Fin (n + 1) → ℝ := fun i => eta F n i
  let h : Fin (n + 1) → ZMod p.val := fun i => (Q.offset i : ZMod p.val)
  let B : ℝ := baselinePrime F n p.val
  let C : ℝ := ((p.val : ℝ) * B)⁻¹
  let pairSum : ℝ :=
    ∑ birth : Fin (n + 1), ∑ stop ∈ Finset.univ.filter (fun stop : Fin (n + 1) => birth < stop),
      η birth * η stop * (if h birth = h stop then 1 else 0) *
        ∏ t ∈ Finset.univ.filter (fun t : Fin (n + 1) => birth < t ∧ t < stop),
          (1 - η t * if h t = h birth then 1 else 0)
  let pairTerm : Fin (n + 1) → Fin (n + 1) → ℝ := fun birth stop =>
    if birth < stop ∧ h birth = h stop then
      C * η birth * η stop *
        ∏ t ∈ Finset.univ.filter (fun t : Fin (n + 1) => birth < t ∧ t < stop),
          (1 - η t * if h t = h birth then 1 else 0)
    else 0
  have hcast (i j : Fin (n + 1)) :
      ((Q.offset i - Q.offset j : ℤ) : ZMod p.val) = 0 ↔ h i = h j := by
    simpa [h] using intCast_sub_eq_zero_iff (Q.offset i) (Q.offset j)
  have hvalid (birth stop : Fin (n + 1)) :
      Q.spanValid g p (some (birth, stop)) ↔ birth < stop ∧ h birth = h stop := by
    unfold ResiduePath.spanValid
    rw [hactive]
    constructor
    · rintro ⟨_, hlt, _, hres, _⟩
      exact ⟨hlt rfl, ((hcast stop birth).mp hres).symm⟩
    · rintro ⟨hlt, hres⟩
      refine ⟨hlt.le, ?_, by simp, (hcast stop birth).mpr hres.symm, by simp⟩
      intro _
      exact hlt
  have hpcast : (p.val : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne p.val)
  have hweight (birth stop : Fin (n + 1)) :
      Q.spanWeight g p (some (birth, stop)) = pairTerm birth stop := by
    by_cases hpairs : birth < stop ∧ h birth = h stop
    · rw [ResiduePath.spanWeight, if_pos ((hvalid birth stop).2 hpairs)]
      simp_rw [hcast]
      simp only [pairTerm, if_pos hpairs]
      rw [hactive]
      have hfilter :
          Finset.univ.filter (fun t : Fin (n + 1) =>
            birth < t ∧ t < stop ∧ t ∉ (∅ : Finset (Fin (n + 1)))) =
          Finset.univ.filter (fun t : Fin (n + 1) => birth < t ∧ t < stop) := by
        ext t
        simp
      rw [hfilter]
      rw [show baselinePrime F n p.val = B by rfl]
      change C * (-η birth) * (-η stop) * _ = C * η birth * η stop * _
      ring
    · rw [ResiduePath.spanWeight, if_neg (fun hv => hpairs ((hvalid birth stop).1 hv))]
      simp only [pairTerm, if_neg hpairs]
  have hspan :
      (∑ span : PrimeSpan n, Q.spanWeight g p span) =
        1 + C * pairSum := by
    rw [Fintype.sum_option]
    have hnone : Q.spanWeight g p none = 1 := by
      simp [ResiduePath.spanWeight, hactive]
    rw [hnone, Fintype.sum_prod_type]
    simp_rw [hweight]
    have hinner (birth : Fin (n + 1)) :
        (∑ stop : Fin (n + 1), pairTerm birth stop) =
          C * ∑ stop ∈ Finset.univ.filter (fun stop : Fin (n + 1) => birth < stop),
            η birth * η stop * (if h birth = h stop then 1 else 0) *
              ∏ t ∈ Finset.univ.filter (fun t : Fin (n + 1) => birth < t ∧ t < stop),
                (1 - η t * if h t = h birth then 1 else 0) := by
      simp only [pairTerm]
      rw [Finset.sum_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro stop _
      by_cases hlt : birth < stop
      · by_cases heq : h birth = h stop
        · simp [hlt, heq]
          <;> ring
        · simp [hlt, heq]
          <;> ring
      · simp [hlt]
    have hdouble :
        (∑ birth : Fin (n + 1), ∑ stop : Fin (n + 1), pairTerm birth stop) =
          ∑ birth : Fin (n + 1), C *
            (∑ stop ∈ Finset.univ.filter (fun stop : Fin (n + 1) => birth < stop),
              η birth * η stop * (if h birth = h stop then 1 else 0) *
                ∏ t ∈ Finset.univ.filter (fun t : Fin (n + 1) => birth < t ∧ t < stop),
                  (1 - η t * if h t = h birth then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro birth _
      exact hinner birth
    rw [hdouble, Finset.mul_sum]
  have hbase_formula : B = 1 - (p.val : ℝ)⁻¹ * ∑ i : Fin (n + 1), η i := by
    rfl
  have hexp := Erdos821.Blueprint.Graph.orphan_expansion p.val (n + 1) η h
  have hexpectation :
      onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) =
        B + (p.val : ℝ)⁻¹ * pairSum := by
    have hraw :
        onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) =
        (p.val : ℝ)⁻¹ * ∑ r : ZMod p.val, ∏ i : Fin (n + 1),
          (1 - η i * if r + h i = 0 then 1 else 0) := by
      simp [onePrimeExpectation, hactive, η, h]
    rw [hraw, hexp, hbase_formula]
  rw [hspan, hexpectation]
  dsimp [C, B]
  field_simp [hbase, hpcast]
  <;> ring

/-- Reindex the active prime's valid lifespans by their optional ghost endpoints. -/
theorem active_span_sum_formula
    (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (g : P.BigGroup) (p : P.Prime g.val)
    (hbase : baselinePrime F n p.val ≠ 0)
    (hnonempty : Q.activeVisits g p ≠ ∅) :
    (∑ span : PrimeSpan n, Q.spanWeight g p span) =
      (baselinePrime F n p.val)⁻¹ *
        onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
  classical
  let η : Fin (n + 1) → ℝ := fun i => eta F n i
  let h : Fin (n + 1) → ZMod p.val := fun i => (Q.offset i : ZMod p.val)
  let active : Finset (Fin (n + 1)) := Q.activeVisits g p
  have hne : active.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnonempty
  let a : Fin (n + 1) := active.min' hne
  let z : Fin (n + 1) := active.max' hne
  have ha : a ∈ active := Finset.min'_mem active hne
  have hz : z ∈ active := Finset.max'_mem active hne
  have hfirst : ∀ i ∈ active, a ≤ i := by
    intro i hi
    exact Finset.min'_le active i hi
  have hlast : ∀ i ∈ active, i ≤ z := by
    intro i hi
    exact Finset.le_max' active i hi
  have haz : a ≤ z := Finset.min'_le_max' active hne
  let B : ℝ := baselinePrime F n p.val
  let f : Fin (n + 1) → ℝ := fun i => η i * if h i = h a then 1 else 0
  let birthCode : Fin (n + 1) → Option (Fin (n + 1)) :=
    fun birth => if birth = a then none else some birth
  let stopCode : Fin (n + 1) → Option (Fin (n + 1)) :=
    fun stop => if stop = z then none else some stop
  let T : Option (Fin (n + 1)) → Option (Fin (n + 1)) → ℝ :=
    activeSpanTerm p.val (n + 1) η h active a z
  have hcast (i j : Fin (n + 1)) :
      ((Q.offset i - Q.offset j : ℤ) : ZMod p.val) = 0 ↔ h i = h j := by
    simpa [h] using intCast_sub_eq_zero_iff (Q.offset i) (Q.offset j)
  have hcastZ (i j : Fin (n + 1)) :
      (Q.offset i : ZMod p.val) - (Q.offset j : ZMod p.val) = 0 ↔ h i = h j := by
    change h i - h j = 0 ↔ h i = h j
    exact sub_eq_zero
  have hfilterEmpty (x : Fin (n + 1)) :
      Finset.univ.filter (fun i : Fin (n + 1) => x < i ∧ i < x) = ∅ := by
    ext i
    constructor
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact False.elim ((lt_irrefl x) (lt_trans hi.1 hi.2))
    · intro hi
      simp at hi
  have hprefixSome (birth : Fin (n + 1)) (hlt : birth < a) :
      prefixChoice a f (some birth) =
        -f birth * ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => birth < i ∧ i < a),
          (1 - f i) := by
    simp [prefixChoice, hlt]
  have hsuffixSome (stop : Fin (n + 1)) (hlt : z < stop) :
      suffixChoice z f (some stop) =
        -f stop * ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => z < i ∧ i < stop),
          (1 - f i) := by
    simp [suffixChoice, hlt]
  have hcompat_of_valid (birth stop : Fin (n + 1))
      (hv : Q.spanValid g p (some (birth, stop))) :
      (∀ i ∈ active, h i = h a) ∧ h birth = h a ∧ h stop = h a ∧
        birth ≤ a ∧ z ≤ stop := by
    rcases hv with ⟨_, _, hinside, hstop, hhit⟩
    have hbirthA : h birth = h a := by
      exact ((hcast a birth).mp (hhit a ha)).symm
    have hstopA : h stop = h a := by
      have hstopB := (hcast stop birth).mp hstop
      have hAB := (hcast a birth).mp (hhit a ha)
      exact hstopB.trans hAB.symm
    refine ⟨?_, hbirthA, hstopA, (hinside a ha).1, (hinside z hz).2⟩
    intro i hi
    have hiB := (hcast i birth).mp (hhit i hi)
    have hAB := (hcast a birth).mp (hhit a ha)
    exact hiB.trans hAB.symm
  have hprod (birth stop : Fin (n + 1))
      (hv : Q.spanValid g p (some (birth, stop))) :
      (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) =>
        birth < i ∧ i < stop ∧ i ∉ active),
          (1 - η i * if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 then 1 else 0)) =
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => birth < i ∧ i < a), (1 - f i)) *
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) =>
          a < i ∧ i < z ∧ i ∉ active), (1 - f i)) *
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => z < i ∧ i < stop), (1 - f i)) := by
    obtain ⟨_, hbirthA, _, hba, hze⟩ := hcompat_of_valid birth stop hv
    have hfactor (i : Fin (n + 1)) :
        (1 - η i * if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 then 1 else 0) =
          1 - f i := by
      rw [Int.cast_sub]
      simp [hcastZ i birth, hbirthA, f]
    calc
      _ = ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) =>
          birth < i ∧ i < stop ∧ i ∉ active), (1 - f i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hfactor i
      _ = _ := span_interval_product_split birth stop a z active (fun i => 1 - f i)
        hba haz hze ha hz hfirst hlast
  have hprefix (birth stop : Fin (n + 1))
      (hv : Q.spanValid g p (some (birth, stop))) :
      prefixChoice a f (birthCode birth) =
        (if birth ∈ active then 1 else -η birth) *
          ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => birth < i ∧ i < a), (1 - f i) := by
    obtain ⟨_, hbirthA, _, hba, _⟩ := hcompat_of_valid birth stop hv
    by_cases heq : birth = a
    · subst birth
      rw [hfilterEmpty a]
      simp [birthCode, prefixChoice, ha]
    · have hlt : birth < a := lt_of_le_of_ne hba heq
      have hnot : birth ∉ active := by
        intro hi
        exact (not_lt_of_ge (hfirst birth hi)) hlt
      have hf : f birth = η birth := by simp [f, hbirthA]
      simp [birthCode, prefixChoice, heq, hlt, hnot, hf]
      <;> ring
  have hsuffix (birth stop : Fin (n + 1))
      (hv : Q.spanValid g p (some (birth, stop))) :
      suffixChoice z f (stopCode stop) =
        (if stop ∈ active then 1 else -η stop) *
          ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => z < i ∧ i < stop), (1 - f i) := by
    obtain ⟨_, _, hstopA, _, hze⟩ := hcompat_of_valid birth stop hv
    by_cases heq : stop = z
    · subst stop
      rw [hfilterEmpty z]
      simp [stopCode, suffixChoice, hz]
    · have hlt : z < stop := lt_of_le_of_ne hze (Ne.symm heq)
      have hnot : stop ∉ active := by
        intro hi
        exact (not_lt_of_ge (hlast stop hi)) hlt
      have hf : f stop = η stop := by simp [f, hstopA]
      simp [stopCode, suffixChoice, heq, hlt, hnot, hf]
      <;> ring
  have hTformula (birth stop : Fin (n + 1))
      (hall : ∀ i ∈ active, h i = h a) :
      T (birthCode birth) (stopCode stop) =
        (p.val : ℝ)⁻¹ * prefixChoice a f (birthCode birth) *
          (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) =>
            a < i ∧ i < z ∧ i ∉ active), (1 - f i)) *
          suffixChoice z f (stopCode stop) := by
    dsimp [T, activeSpanTerm, f]
    rw [if_pos hall]
  have hpcast : (p.val : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne p.val)
  have hweight (birth stop : Fin (n + 1)) :
      Q.spanWeight g p (some (birth, stop)) = B⁻¹ * T (birthCode birth) (stopCode stop) := by
    by_cases hv : Q.spanValid g p (some (birth, stop))
    · obtain ⟨hall, hbirthA, hstopA, hba, hze⟩ := hcompat_of_valid birth stop hv
      rw [ResiduePath.spanWeight, if_pos hv, hprod birth stop hv]
      rw [hTformula birth stop hall, hprefix birth stop hv, hsuffix birth stop hv]
      rw [show baselinePrime F n p.val = B by rfl]
      dsimp [B]
      field_simp [hbase, hpcast]
      <;> ring
    · rw [ResiduePath.spanWeight, if_neg hv]
      have hTzero : T (birthCode birth) (stopCode stop) = 0 := by
        by_cases hall : ∀ i ∈ active, h i = h a
        · by_contra hT
          have hprefixNe : prefixChoice a f (birthCode birth) ≠ 0 := by
            intro hzero
            apply hT
            rw [hTformula birth stop hall, hzero]
            simp
          have hsuffixNe : suffixChoice z f (stopCode stop) ≠ 0 := by
            intro hzero
            apply hT
            rw [hTformula birth stop hall, hzero]
            simp
          have hba : birth ≤ a := by
            by_cases heq : birth = a
            · simpa [heq]
            · by_contra hnot
              have hlt : a < birth := lt_of_not_ge hnot
              have hcode : birthCode birth = some birth := by simp [birthCode, heq]
              apply hprefixNe
              rw [hcode]
              simp only [prefixChoice, if_neg (not_lt_of_ge hlt.le)]
          have hze : z ≤ stop := by
            by_cases heq : stop = z
            · rw [heq]
            · by_contra hnot
              have hlt : stop < z := lt_of_not_ge hnot
              have hcode : stopCode stop = some stop := by simp [stopCode, heq]
              apply hsuffixNe
              rw [hcode]
              simp only [suffixChoice, if_neg (not_lt_of_ge hlt.le)]
          have hbirthA : h birth = h a := by
            by_cases heq : birth = a
            · simp [heq]
            · have hlt : birth < a := lt_of_le_of_ne hba heq
              have hcode : birthCode birth = some birth := by simp [birthCode, heq]
              have hf : f birth ≠ 0 := by
                intro hf
                apply hprefixNe
                rw [hcode]
                rw [hprefixSome birth hlt, hf]
                simp
              by_contra hneq
              apply hf
              simp [f, hneq]
          have hstopA : h stop = h a := by
            by_cases heq : stop = z
            · subst stop
              exact hall z hz
            · have hlt : z < stop := lt_of_le_of_ne hze (Ne.symm heq)
              have hcode : stopCode stop = some stop := by simp [stopCode, heq]
              have hf : f stop ≠ 0 := by
                intro hf
                apply hsuffixNe
                rw [hcode]
                rw [hsuffixSome stop hlt, hf]
                simp
              by_contra hneq
              apply hf
              simp [f, hneq]
          have hvalid_from_T : Q.spanValid g p (some (birth, stop)) := by
            unfold ResiduePath.spanValid
            refine ⟨le_trans hba (le_trans haz hze), ?_, ?_, ?_, ?_⟩
            · intro hempty
              exact (hnonempty hempty).elim
            · intro i hi
              exact ⟨le_trans hba (hfirst i hi), le_trans (hlast i hi) hze⟩
            · exact (hcast stop birth).mpr (hstopA.trans hbirthA.symm)
            · intro i hi
              exact (hcast i birth).mpr ((hall i hi).trans hbirthA.symm)
          exact hv hvalid_from_T
        · simp [T, activeSpanTerm, hall]
      simp [hTzero]
  have hnone : Q.spanWeight g p none = 0 := by
    simp [ResiduePath.spanWeight, active, hnonempty]
  have hzero_birth (stop : Option (Fin (n + 1))) : T (some a) stop = 0 := by
    simp [T, activeSpanTerm, prefixChoice]
  have hzero_stop (birth : Option (Fin (n + 1))) : T birth (some z) = 0 := by
    simp [T, activeSpanTerm, suffixChoice]
  have hrecode :
      (∑ birth : Option (Fin (n + 1)), ∑ stop : Option (Fin (n + 1)), T birth stop) =
        ∑ birth : Fin (n + 1), ∑ stop : Fin (n + 1),
          T (birthCode birth) (stopCode stop) := by
    calc
      _ = ∑ birth : Option (Fin (n + 1)), ∑ stop : Fin (n + 1),
          T birth (stopCode stop) := by
        apply Finset.sum_congr rfl
        intro birth _
        exact option_sum_recode z (T birth) (hzero_stop birth)
      _ = _ := by
        exact option_sum_recode a
          (fun birth : Option (Fin (n + 1)) =>
            ∑ stop : Fin (n + 1), T birth (stopCode stop))
          (by simp [hzero_birth])
  have hactiveSum :
      (∑ birth : Option (Fin (n + 1)), ∑ stop : Option (Fin (n + 1)), T birth stop) =
        onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
    simpa [T, η, h, active] using
      Erdos821.S2Core.active_span_sum p.val (n + 1) η h active a z ha hz hfirst hlast
  have hscale :
      (∑ birth : Fin (n + 1), ∑ stop : Fin (n + 1),
        B⁻¹ * T (birthCode birth) (stopCode stop)) =
        B⁻¹ * ∑ birth : Fin (n + 1), ∑ stop : Fin (n + 1),
          T (birthCode birth) (stopCode stop) := by
    calc
      _ = ∑ birth : Fin (n + 1), B⁻¹ * ∑ stop : Fin (n + 1),
          T (birthCode birth) (stopCode stop) := by
        apply Finset.sum_congr rfl
        intro birth _
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.mul_sum]
  calc
    (∑ span : PrimeSpan n, Q.spanWeight g p span) =
        B⁻¹ * ∑ birth : Option (Fin (n + 1)), ∑ stop : Option (Fin (n + 1)), T birth stop := by
      rw [Fintype.sum_option, hnone]
      simp only [zero_add]
      rw [Fintype.sum_prod_type]
      simp_rw [hweight]
      calc
        _ = ∑ birth : Fin (n + 1), ∑ stop : Fin (n + 1),
            B⁻¹ * T (birthCode birth) (stopCode stop) := rfl
        _ = B⁻¹ * ∑ birth : Fin (n + 1), ∑ stop : Fin (n + 1),
            T (birthCode birth) (stopCode stop) := hscale
        _ = B⁻¹ * ∑ birth : Option (Fin (n + 1)), ∑ stop : Option (Fin (n + 1)),
            T birth stop := congrArg (fun x : ℝ => B⁻¹ * x) hrecode.symm
    _ = _ := by
      rw [hactiveSum]

end Erdos821.P3Sum

namespace Erdos821.S2Core

/-- Exact finite one-prime lifespan sum, in the active and orphan cases. -/
theorem SpanSumTask_proof : SpanSumTask := by
  intro F P J m n A Q g p hbase
  by_cases hactive : Q.activeVisits g p = ∅
  · exact Erdos821.P3Sum.inactive_span_sum F P J m n A Q g p hbase hactive
  · exact Erdos821.P3Sum.active_span_sum_formula F P J m n A Q g p hbase hactive


end Erdos821.S2Core
