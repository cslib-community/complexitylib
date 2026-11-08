/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Structure
public import Complexity.Logics.Propositional.CSP.Edge.Size
import Complexity.Foundations.Data.List.Blocks
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic

/-!
# Ordered scope and port accounting for whole-instance contraction

The actual index projection equals deletion of all internal variables in scope order.
The fresh connector is appended once per touched original constraint.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset

variable {F : CSP Table ℕ}

/-- The outside index projection is precisely the original scope with internal names deleted. -/
theorem outsideScope_eq_filter (vs scope : List ℕ) :
    ((outsidePositions scope.length (positions vs scope)).map fun j => scope.getD j 0) =
      scope.filter (fun v => !vs.contains v) := by
  have he : outsidePositions scope.length (positions vs scope) =
      (List.range scope.length).filter (fun j => !vs.contains (scope.getD j 0)) := by
    unfold outsidePositions
    apply List.filter_congr
    intro j hj
    have hb := List.mem_range.mp hj
    simp [positions, hb]
  rw [he]
  have hf := List.filter_map (f := fun j => scope.getD j 0)
    (p := fun v => !vs.contains v) (l := List.range scope.length)
  simp only [Function.comp_def] at hf
  rw [← hf, List.map_getD_range]

/-- No selected coordinate means that deletion leaves the whole ordered scope unchanged. -/
theorem filter_eq_self_of_positions_empty {vs scope : List ℕ}
    (hp : positions vs scope = []) : scope.filter (fun v => !vs.contains v) = scope := by
  rw [← outsideScope_eq_filter]
  simp only [hp, outsidePositions, List.contains_nil, Bool.not_false, List.filter_true]
  exact List.map_getD_range scope 0

/-- A touched original scope is nonempty, even before imposing the two-port blossom condition. -/
theorem scope_ne_nil_of_positions_ne_nil {vs scope : List ℕ}
    (hp : positions vs scope ≠ []) : scope ≠ [] := by
  rintro rfl
  exact hp rfl

/-- The scope at an old constraint deletes all internal variables and appends its own fresh
connector exactly when touched. Outside order and original constraint multiplicity are retained. -/
theorem scope_constraint (f : OccurrenceLabeling F Bool) (vs : List ℕ) (i : Fin F.length) :
    (constraint f vs i).2 = F[i.val].2.filter (fun v => !vs.contains v) ++
      if (positions vs F[i.val].2).isEmpty then [] else [connector F i] := by
  unfold constraint
  split
  next hp =>
    have he := List.isEmpty_iff.mp hp
    simpa only [List.append_nil] using (filter_eq_self_of_positions_empty he).symm
  next hp =>
    dsimp only
    rw [outsideScope_eq_filter]

/-- Positivity at every retained old constraint is unchanged by actual contraction. -/
theorem positive_constraint (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) : (!(constraint f vs i).2.isEmpty) = !F[i.val].2.isEmpty := by
  unfold constraint
  split
  · rfl
  next hp =>
    have he : positions vs F[i.val].2 ≠ [] := by simpa using hp
    have hs := scope_ne_nil_of_positions_ne_nil he
    simp [List.isEmpty_eq_false_iff.mpr hs]

/-- Adding the central nonempty exactly-one scope increases the positive count by exactly one.
Nullary original constraints are preserved and are not charged to this measure. -/
theorem positiveCount_contract (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (hne : touched F vs ≠ []) : (contract f vs).positiveCount = F.positiveCount + 1 := by
  have hscope : connectors F vs ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [length_connectors, List.length_nil, List.length_eq_zero_iff] at hh
    exact hne hh
  have he : ((List.ofFn (constraint f vs)).map fun c => !c.2.isEmpty) =
      F.map (fun c => !c.2.isEmpty) := by
    simp only [List.map_ofFn, Function.comp_def]
    have hp : (fun i => !(constraint f vs i).2.isEmpty) =
        (fun i : Fin F.length => !F[i.val].2.isEmpty) := funext (positive_constraint f vs)
    rw [hp]
    exact List.ofFn_getElem_eq_map F (fun c => !c.2.isEmpty)
  have hcount := congrArg (List.countP id) he
  simp only [List.countP_map, Function.comp_def, id_eq] at hcount
  simpa [positiveCount, contract, List.filter_append, List.isEmpty_eq_false_iff.mpr hscope,
    ← List.countP_eq_length_filter] using hcount

/-- Touching is determined by the gathered ports, not by the number of cycle visits. -/
theorem mem_touched (vs : List ℕ) (i : Fin F.length) :
    i ∈ touched F vs ↔ positions vs F[i.val].2 ≠ [] := by
  simp [touched]

/-- Any nonempty incidence sequence touches an actual original constraint. -/
theorem touched_ne_nil (w : Walk F) (hne : w.steps ≠ []) : touched F (internal w) ≠ [] := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
  have ho : s.1 ∈ w.edges := List.mem_flatMap.mpr ⟨s, hs, by simp⟩
  have hv : s.1.var ∈ internal w := List.mem_dedup.mpr (List.mem_map.mpr ⟨s.1, ho, rfl⟩)
  have hp := (mem_positions (internal w) s.1.1 s.1.2).mpr hv
  exact List.ne_nil_of_mem ((mem_touched _ _).mpr (List.ne_nil_of_mem hp))

/-- The actual output variable set consists of surviving old names and the fresh connectors. -/
theorem vars_contract (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (contract f vs).vars.toFinset =
      (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
  ext v
  simp only [List.mem_toFinset, mem_union, mem_sdiff]
  constructor
  · intro hv
    obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      rw [scope_constraint] at hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨hm, hn⟩ := List.mem_filter.mp hv
        exact Or.inl ⟨List.mem_flatMap.mpr ⟨F[i.val], List.getElem_mem i.isLt, hm⟩,
          by simpa using hn⟩
      · split at hv
        · cases hv
        next hp =>
          have he := List.mem_singleton.mp hv
          refine Or.inr (List.mem_map.mpr ⟨i, ?_, he.symm⟩)
          exact (mem_touched vs i).mpr (by simpa using hp)
    · have he := List.mem_singleton.mp hc
      subst c
      exact Or.inr hv
  · rintro (⟨hv, hn⟩ | hv)
    · obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr hv
      apply List.mem_flatMap.mpr
      refine ⟨constraint f vs o.1, List.mem_append_left _ (List.mem_ofFn.mpr ⟨o.1, rfl⟩), ?_⟩
      rw [scope_constraint]
      apply List.mem_append_left
      apply List.mem_filter.mpr
      exact ⟨List.getElem_mem o.2.isLt, by simpa using hn⟩
    · exact List.mem_flatMap.mpr ⟨(exactlyOne (connectors F vs), connectors F vs),
        List.mem_append_right _ (List.mem_singleton_self _), hv⟩

/-- Freshness makes the output variable count an exact deletion-plus-connectors formula. -/
theorem numVars_contract (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (contract f vs).numVars = (F.vars.toFinset \ vs.toFinset).card + (touched F vs).length := by
  have hd : Disjoint (F.vars.toFinset \ vs.toFinset) (connectors F vs).toFinset := by
    apply disjoint_left.mpr
    intro v hv hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact connector_not_mem i (List.mem_toFinset.mp (mem_sdiff.mp hv).1)
  rw [numVars, vars_contract, card_union_of_disjoint hd,
    List.toFinset_card_of_nodup (nodup_connectors F vs), length_connectors]

/-- Exact finite accounting when all deleted variables actually occurred in the old instance. -/
theorem numVars_contract_add (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (hv : vs.toFinset ⊆ F.vars.toFinset) :
    (contract f vs).numVars + vs.toFinset.card = F.numVars + (touched F vs).length := by
  have hc := card_sdiff_add_card_eq_card hv
  rw [numVars_contract]
  unfold numVars
  omega

/-- Collecting the new port of each touched constraint gives precisely the central scope. -/
theorem flatMap_connectors (F : CSP Table ℕ) (vs : List ℕ) :
    (List.finRange F.length).flatMap (fun i =>
      if (positions vs F[i.val].2).isEmpty then [] else [connector F i]) = connectors F vs := by
  have he (is : List (Fin F.length)) :
      is.flatMap (fun i => if (positions vs F[i.val].2).isEmpty then [] else [connector F i]) =
        (is.filter fun i => !(positions vs F[i.val].2).isEmpty).map (connector F) := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      cases hp : (positions vs F[i.val].2).isEmpty <;>
        simp only [List.flatMap_cons, List.filter_cons, hp, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, ih, List.nil_append, List.singleton_append, List.map_cons]
  exact he _

/-- Occurrence multiplicities are exactly old outside occurrences plus two copies of the
connector scope. This permutation does not reorder the constructed CSP itself. -/
theorem vars_contract_perm (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (contract f vs).vars.Perm
      (F.vars.filter (fun v => !vs.contains v) ++ connectors F vs ++ connectors F vs) := by
  let ids := List.finRange F.length
  let outside (i : Fin F.length) := F[i.val].2.filter fun v => !vs.contains v
  let added (i : Fin F.length) :=
    if (positions vs F[i.val].2).isEmpty then [] else [connector F i]
  have hf : ids.map (fun i => F[i.val]) = F := by
    rw [← List.ofFn_eq_map]
    simp
  have hflat := congrArg (List.flatMap Prod.snd) hf
  simp only [List.flatMap_map] at hflat
  have hout : ids.flatMap outside = F.vars.filter (fun v => !vs.contains v) := by
    rw [show ids.flatMap outside =
      (ids.flatMap fun i => F[i.val].2).filter (fun v => !vs.contains v) from
        List.filter_flatMap.symm]
    exact congrArg (List.filter fun v => !vs.contains v) hflat
  have hscope : (List.ofFn (constraint f vs)).flatMap Prod.snd =
      ids.flatMap (fun i => outside i ++ added i) := by
    rw [List.ofFn_eq_map, List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    exact scope_constraint f vs i
  have he : (contract f vs).vars =
      ids.flatMap (fun i => outside i ++ added i) ++ connectors F vs := by
    simp only [contract, vars, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hscope]
  rw [he]
  have hp := (List.flatMap_append_perm ids outside added).symm.append_right (connectors F vs)
  simpa only [hout, show ids.flatMap added = connectors F vs from flatMap_connectors F vs]
    using hp

/-- Each output name retains its two old outside occurrences, or is a fresh connector with
one old-constraint port and one central port. No enumeration below a binary name is involved. -/
theorem count_vars_contract (f : OccurrenceLabeling F Bool) (vs : List ℕ) (v : ℕ) :
    (contract f vs).vars.count v =
      (if v ∈ vs then 0 else F.vars.count v) + 2 * (connectors F vs).count v := by
  rw [(vars_contract_perm f vs).count_eq]
  simp only [List.count_append]
  by_cases hv : v ∈ vs
  · have hz : (F.vars.filter fun w => !vs.contains w).count v = 0 := by
      simp [List.count_eq_zero, hv]
    simp only [hv, ↓reduceIte, hz]
    omega
  · rw [List.count_filter (by simpa using hv)]
    simp only [hv, ↓reduceIte]
    omega

/-- Actual contraction preserves the edge-instance model at arbitrary finite table arities. -/
theorem edge_contract (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    EdgeInstance (contract f vs) := by
  apply edgeInstance_of_count_vars
  · intro i
    have hi : (contract f vs)[i.val] ∈ contract f vs := List.getElem_mem i.isLt
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi
      rw [← hj]
      unfold constraint
      split
      · exact hF.scope_nodup j
      · dsimp only
        rw [outsideScope_eq_filter]
        apply List.nodup_append.mpr
        refine ⟨(hF.scope_nodup j).filter _, by simp, ?_⟩
        intro a ha b hb he
        have hb' := List.mem_singleton.mp hb
        apply connector_not_mem j
        have hm := (List.mem_filter.mp ha).1
        exact (he.trans hb') ▸ List.mem_flatMap.mpr
          ⟨F[j.val], List.getElem_mem j.isLt, hm⟩
    · rw [List.mem_singleton.mp hi]
      exact nodup_connectors F vs
  · intro v hv
    rw [count_vars_contract]
    have hm : v ∈ (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
      rw [← vars_contract f vs]
      exact List.mem_toFinset.mpr hv
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨hv, hn⟩ := mem_sdiff.mp hm
      have hnew : v ∉ connectors F vs := by
        intro hh
        obtain ⟨i, hi, he⟩ := List.mem_map.mp hh
        exact connector_not_mem i (he ▸ List.mem_toFinset.mp hv)
      rw [ite_eq_right (by simpa using hn), hF.count_vars (List.mem_toFinset.mp hv),
        List.count_eq_zero.mpr hnew]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      have hz : F.vars.count (connector F i) = 0 := List.count_eq_zero.mpr (connector_not_mem i)
      have hc : (connectors F vs).count (connector F i) = 1 :=
        List.count_eq_one_of_mem (nodup_connectors F vs) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      rw [hz, hc]
      split <;> rfl

end Cslib.Logic.PL.CSP.Blossom
