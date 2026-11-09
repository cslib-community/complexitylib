/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Table
public import Complexity.Logics.Propositional.CSP.Boolean
public import Complexity.Foundations.Data.BitString.DeltaMatroid.Composition
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Even delta-matroid table relations

The relations here are exactly `CSP.booleanRelation Table.arity Table.sem`, including the
existing declared-width and well-formedness guards. Exactly-one has odd common parity and
requires a nonempty scope. Local contraction follows Section 5.3, printed pp. 12–13 of
[KazdaKolmogorovRolinek2018], arXiv v6: a feasible reference and distinct in-range internal
positions suffice for the local closure. The star composition is transported back to the actual
outside-coordinate order with the connector last, using `Table.sem_contract_cases` rather than
reproving the operation semantics. No blossom invariant or solver is assumed. The generic
exactly-one result corresponds to Example 17, printed p. 7; the empty scope is excluded as
required by the nonempty convention in Definition 5.

## Main results

* `booleanRelation_exactlyOne`: identifies the actual table relation with exactly-one.
* `isEvenDeltaMatroid_exactlyOne`: arbitrary nonempty connector scope.
* `not_isDeltaMatroid_exactlyOne_nil`: zero connectors are rejected.
* `isEvenDeltaMatroid_contract`: closure of the actual guarded local contraction.
-/

public section

namespace Cslib.Logic.PL.CSP.Table

open Cslib.BitString

private theorem oneHot_eq_ofFn (width : ℕ) (i : Fin width) :
    oneHot width i = List.ofFn (fun j : Fin width => decide (j = i)) := by
  apply List.ext_getElem
  · simp [oneHot]
  · intro j hj hk
    simp [oneHot, Fin.ext_iff, eq_comm]

/-- The guarded table relation is precisely the usual exactly-one relation. -/
theorem booleanRelation_exactlyOne {V : Type*} (scope : List V) :
    booleanRelation arity sem (exactlyOne scope) = oneHotRelation (Fin scope.length) := by
  change {x : Fin scope.length → Bool | (exactlyOne scope).sem (List.ofFn x) = true} = _
  ext x
  change (exactlyOne scope).sem (List.ofFn x) = true ↔ _
  rw [sem_eq_true, wellFormed_exactlyOne]
  simp only [true_and, exactlyOne, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [oneHot_eq_ofFn scope.length ⟨i, hi⟩] at he
    exact List.ofFn_injective he
  · rintro ⟨i, hi⟩
    change (fun j => decide (j = i)) = x at hi
    exact ⟨i, i.isLt, by rw [oneHot_eq_ofFn scope.length i, hi]⟩

/-- The new connector table is an even delta-matroid for every nonempty scope.
Repeated names in the supplied scope do not change this local relation claim. -/
theorem isEvenDeltaMatroid_exactlyOne {V : Type*} (scope : List V) (hne : scope ≠ []) :
    IsEvenDeltaMatroid (booleanRelation arity sem (exactlyOne scope)) := by
  rw [booleanRelation_exactlyOne]
  have hp : 0 < scope.length := List.length_pos_iff.mpr hne
  change IsEvenDeltaMatroid (oneHotRelation (Fin scope.length))
  let : Nonempty (Fin scope.length) := ⟨⟨0, hp⟩⟩
  exact isEvenDeltaMatroid_oneHotRelation

/-- Zero connectors give the empty relation, excluded by the nonempty delta-matroid convention. -/
theorem not_isDeltaMatroid_exactlyOne_nil {V : Type*} :
    ¬ IsDeltaMatroid (booleanRelation arity sem (exactlyOne ([] : List V))) := by
  rw [booleanRelation_exactlyOne]
  intro h
  obtain ⟨x, i, hi⟩ := h.nonempty
  exact Fin.elim0 i

private theorem outside_mem {width : ℕ} {positions : List ℕ} {i : ℕ} :
    i ∈ outsidePositions width positions ↔ i < width ∧ i ∉ positions := by
  simp [outsidePositions]

private def outsideCoord {width : ℕ} (positions : List ℕ)
    (j : Fin (outsidePositions width positions).length) : Fin width :=
  ⟨(outsidePositions width positions)[j],
    (outside_mem.mp (List.getElem_mem j.isLt)).1⟩

private def insideCoord {width : ℕ} {positions : List ℕ}
    (h : validPositions width positions = true) (j : Fin positions.length) : Fin width :=
  ⟨positions[j], (validPositions_eq_true.mp h).2 _ (List.getElem_mem j.isLt)⟩

private noncomputable def splitEquiv {width : ℕ} {positions : List ℕ}
    (h : validPositions width positions = true) :
    Fin (outsidePositions width positions).length ⊕ Fin positions.length ≃ Fin width :=
  Equiv.ofBijective (Sum.elim (outsideCoord positions) (insideCoord h)) (by
    constructor
    · intro i j he
      rcases i with i | i <;> rcases j with j | j
      · apply congrArg Sum.inl
        apply (List.nodup_range.filter (fun i => !positions.contains i)).injective_get
        exact congrArg Fin.val he
      · have ho := (outside_mem.mp (List.getElem_mem i.isLt)).2
        have he' : (outsidePositions width positions)[i] = positions[j] :=
          congrArg Fin.val he
        exact (ho (he'.symm ▸ List.getElem_mem j.isLt)).elim
      · have ho := (outside_mem.mp (List.getElem_mem j.isLt)).2
        have he' : positions[i] = (outsidePositions width positions)[j] :=
          congrArg Fin.val he
        exact (ho (he' ▸ List.getElem_mem i.isLt)).elim
      · apply congrArg Sum.inr
        apply (validPositions_eq_true.mp h).1.injective_get
        exact congrArg Fin.val he
    · intro i
      by_cases hi : i.val ∈ positions
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
        exact ⟨.inr j, Fin.ext hj⟩
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp (outside_mem.mpr ⟨i.isLt, hi⟩)
        exact ⟨.inl j, Fin.ext hj⟩)

private theorem project_ofFn {width : ℕ} (positions : List ℕ) (x : Fin width → Bool) :
    project (List.ofFn x) (outsidePositions width positions) =
      List.ofFn (fun j => x (outsideCoord positions j)) := by
  apply List.ext_getElem
  · simp [project]
  · intro j hj hk
    have hj' : j < (outsidePositions width positions).length := by simpa using hk
    have hb := (outside_mem.mp (List.getElem_mem hj')).1
    simp [project, outsideCoord, hb]

private theorem deviations_eq_count {width : ℕ} {positions : List ℕ}
    (h : validPositions width positions = true) (reference : List Bool) (x : Fin width → Bool) :
    deviations reference (List.ofFn x) positions =
      (List.ofFn (fun j => x (insideCoord h j) !=
        reference.getD (positions[j]) false)).count true := by
  rw [show List.ofFn (fun j => x (insideCoord h j) != reference.getD (positions[j]) false) =
      positions.map (fun i => (List.ofFn x).getD i false != reference.getD i false) from ?_]
  · simp [deviations, List.count_eq_countP, Function.comp_def]
  · rw [← List.ofFn_getElem_eq_map]
    congr 1
    ext j
    have hb := (validPositions_eq_true.mp h).2 _ (List.getElem_mem j.isLt)
    simp [insideCoord, hb]

private theorem count_eq_zero_iff {n : ℕ} (x : Fin n → Bool) :
    (List.ofFn x).count true = 0 ↔ ∀ i, x i = false := by
  simp only [List.count_eq_zero, List.mem_ofFn, not_exists, Bool.not_eq_true]

private theorem count_eq_one_iff {n : ℕ} (x : Fin n → Bool) :
    (List.ofFn x).count true = 1 ↔ ∃ k, ∀ j, x j = decide (j = k) := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := exists_oneHot_of_count_true h
    have hk' : k < n := by simpa using hk
    have hh : (fun j : Fin n => decide (j = (⟨k, hk'⟩ : Fin n))) = x := by
      apply List.ofFn_injective
      have he' : oneHot n k = List.ofFn x := by simpa only [List.length_ofFn] using he
      rwa [oneHot_eq_ofFn n ⟨k, hk'⟩] at he'
    exact ⟨⟨k, hk'⟩, fun j => congrFun hh.symm j⟩
  · rintro ⟨k, hk⟩
    have he : x = (fun j => decide (j = k)) := funext hk
    rw [he, ← oneHot_eq_ofFn]
    exact count_true_oneHot k.isLt

private def outputEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv

private theorem ofFn_output (n : ℕ) (x : Fin (n + 1) → Bool) :
    List.ofFn x = List.ofFn (fun j => x (outputEquiv n (.inl j))) ++
      [x (outputEquiv n (.inr ()))] := by
  rw [List.ofFn_succ_last]
  rfl

private theorem mem_comp_starAt_iff {m n : ℕ} (R : Set ((Fin m ⊕ Fin n) → Bool))
    (reference : Fin n → Bool) (x : (Fin m ⊕ Unit) → Bool) :
    x ∈ comp R (starAt reference) ↔
      ∃ z : Fin n → Bool, Sum.elim (fun j => x (.inl j)) z ∈ R ∧
        (((List.ofFn (fun j => z j != reference j)).count true = 0 ∧
            x (.inr ()) = false) ∨
          ((List.ofFn (fun j => z j != reference j)).count true = 1 ∧
            x (.inr ()) = true)) := by
  change (∃ z, _ ∧ _) ↔ _
  apply exists_congr
  intro z
  rw [mem_starAt_iff, count_eq_zero_iff, count_eq_one_iff]
  simp only [Sum.elim_inl, Sum.elim_inr, exists_and_right]

/-- Local contraction preserves the actual guarded declared-arity even delta-matroid relation.
A feasible reference supplies compatibility with the star gadget. The selected positions must
be distinct and in range, exactly as required by `canContract`; no blossom condition is used. -/
theorem isEvenDeltaMatroid_contract {table : Table} {reference : List Bool}
    {positions : List ℕ} (hR : IsEvenDeltaMatroid (booleanRelation arity sem table))
    (hc : canContract table reference positions = true) :
    IsEvenDeltaMatroid (booleanRelation arity sem (contract table reference positions)) := by
  obtain ⟨hw, hr, hd, hb⟩ := canContract_eq_true.mp hc
  have href : reference.length = table.arity := wellFormed_eq_true.mp hw _ hr
  have hp : validPositions table.arity positions = true :=
    validPositions_eq_true.mpr ⟨hd, hb⟩
  let m := (outsidePositions table.arity positions).length
  let E := splitEquiv hp
  let R : Set ((Fin m ⊕ Fin positions.length) → Bool) :=
    {x | (fun i => x (E.symm i)) ∈ booleanRelation arity sem table}
  let r : Fin positions.length → Bool := fun j => reference.getD positions[j] false
  let C := comp R (starAt r)
  have hnew : (contract table reference positions).arity = m + 1 := by
    simpa only [m, href] using arity_contract hc
  let F : Fin m ⊕ Unit ≃ Fin (contract table reference positions).arity :=
    (outputEquiv m).trans (finCongr hnew.symm)
  have hrow (y : Fin (contract table reference positions).arity → Bool) :
      List.ofFn y = List.ofFn (fun j => y (F (.inl j))) ++ [y (F (.inr ()))] := by
    rw [List.ofFn_congr hnew y]
    exact ofFn_output m (fun j => y (Fin.cast hnew.symm j))
  have he : {y | (fun i => y (F i)) ∈ C} =
      booleanRelation arity sem (contract table reference positions) := by
    ext y
    change (fun i => y (F i)) ∈ comp R (starAt r) ↔
      (contract table reference positions).sem (List.ofFn y) = true
    rw [mem_comp_starAt_iff]
    rw [sem_contract_cases hc]
    constructor
    · rintro ⟨z, hz, hs⟩
      let old : Fin table.arity → Bool :=
        fun i => Sum.elim (fun j => y (F (.inl j))) z (E.symm i)
      have hsem : table.sem (List.ofFn old) = true := hz
      have hold := (sem_eq_true.mp hsem).2
      have ho : project (List.ofFn old) (outsidePositions reference.length positions) =
          List.ofFn (fun j => y (F (.inl j))) := by
        rw [href, project_ofFn]
        congr 1
        ext j
        exact congrArg (Sum.elim (fun j => y (F (.inl j))) z)
          (E.symm_apply_apply (.inl j))
      have hdv : deviations reference (List.ofFn old) positions =
          (List.ofFn (fun j => z j != r j)).count true := by
        rw [deviations_eq_count hp]
        congr 2
        ext j
        exact congrArg (fun b => b != r j)
          (congrArg (Sum.elim (fun j => y (F (.inl j))) z)
            (E.symm_apply_apply (.inr j)))
      refine ⟨List.ofFn old, hold, ?_⟩
      rcases hs with ⟨hs, hconn⟩ | ⟨hs, hconn⟩
      · exact Or.inl ⟨hdv.trans hs, by rw [ho, hrow, hconn]⟩
      · exact Or.inr ⟨hdv.trans hs, by rw [ho, hrow, hconn]⟩
    · rintro ⟨old, hold, hs⟩
      have hlen : old.length = table.arity := wellFormed_eq_true.mp hw _ hold
      let a : Fin table.arity → Bool := fun i => old.getD i false
      have ha : List.ofFn a = old := by
        apply List.ext_getElem
        · simp [hlen]
        · intro j hj hk
          simp only [List.getElem_ofFn]
          exact (List.getElem_eq_getD false).symm
      let z : Fin positions.length → Bool := fun j => a (insideCoord hp j)
      have hproj : project old (outsidePositions reference.length positions) =
          List.ofFn (fun j => a (outsideCoord positions j)) := by
        rw [href, ← ha, project_ofFn]
      have hdv : deviations reference old positions =
          (List.ofFn (fun j => z j != r j)).count true := by
        rw [← ha, deviations_eq_count hp]
      have hout : ∀ j, a (outsideCoord positions j) = y (F (.inl j)) := by
        have heq : List.ofFn (fun j => a (outsideCoord positions j)) =
            List.ofFn (fun j => y (F (.inl j))) := by
          rcases hs with ⟨_, heq⟩ | ⟨_, heq⟩ <;>
            rw [hproj, hrow] at heq <;> exact (List.append_inj heq (by simp [m])).1
        exact fun j => congrFun (List.ofFn_injective heq) j
      refine ⟨z, ?_, ?_⟩
      · change table.sem (List.ofFn (fun i =>
          Sum.elim (fun j => y (F (.inl j))) z (E.symm i))) = true
        have heq : (fun i => Sum.elim (fun j => y (F (.inl j))) z (E.symm i)) = a := by
          funext i
          obtain ⟨j, rfl⟩ := E.surjective i
          rw [E.symm_apply_apply]
          rcases j with j | j
          · exact (hout j).symm
          · rfl
        rw [heq, ha]
        exact sem_eq_true.mpr ⟨hw, hold⟩
      · rcases hs with ⟨hs, heq⟩ | ⟨hs, heq⟩
        · left
          refine ⟨hdv.symm.trans hs, ?_⟩
          rw [hrow] at heq
          exact List.singleton_injective
            ((List.append_inj heq (by simp [project, href, m])).2).symm
        · right
          refine ⟨hdv.symm.trans hs, ?_⟩
          rw [hrow] at heq
          exact List.singleton_injective
            ((List.append_inj heq (by simp [project, href, m])).2).symm
  have hne : C.Nonempty := by
    have hsem := sem_contract_reference hc
    have hlen :
        (project reference (outsidePositions reference.length positions) ++ [false]).length =
        (contract table reference positions).arity := by
      simpa [project] using (arity_contract hc).symm
    let y : Fin (contract table reference positions).arity → Bool :=
      fun j =>
        (project reference (outsidePositions reference.length positions) ++ [false]).getD j false
    have hy : y ∈ booleanRelation arity sem (contract table reference positions) := by
      change (contract table reference positions).sem (List.ofFn y) = true
      convert hsem using 1
      congr 1
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro j hj hk
        simp only [List.getElem_ofFn]
        exact (List.getElem_eq_getD false).symm
    exact ⟨fun i => y (F i), (Set.ext_iff.mp he y).mpr hy⟩
  rw [← he]
  exact ((hR.reindex E.symm).comp (isEvenDeltaMatroid_starAt r) hne).reindex F

end Cslib.Logic.PL.CSP.Table
