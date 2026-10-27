/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Drawing
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingProfileBounds
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD

/-!
# Uniquely indexed actual variable positions

The finite position table contains each shared source variable once and each private auxiliary
in exactly one clause box. The private signed-clause intervals use the actual compiler's prefix
offsets. Thus table lookup returns the intended position without any auxiliary-name collision.

## Main results

* `positivePositionTable_keys_nodup`: every actual variable has a unique table key.
* `positiveVariablePoint_auxiliary`: actual auxiliary positions resolve to their local boxes.

## References

These support and index arguments are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- Whether a structured variable is private to a clause box. -/
def isAuxiliaryVariable : CNF.PositiveExactOneCompile.Variable ℕ → Bool
  | .inl (.inl _) => false
  | _ => true

/-- The auxiliary role excludes all inherited source-variable names. -/
theorem isAuxiliaryVariable_iff (v : CNF.PositiveExactOneCompile.Variable ℕ) :
    isAuxiliaryVariable v = true ↔ ∀ n, v ≠ Sum.inl (Sum.inl n) := by
  rcases v with (v | v) | v
  · simp [isAuxiliaryVariable]
  · simp [isAuxiliaryVariable]
  · simp [isAuxiliaryVariable]

private theorem auxiliary_block_keys (vs : List (CNF.PositiveExactOneCompile.Variable ℕ))
    (f : CNF.PositiveExactOneCompile.Variable ℕ → CNF.PositiveExactOneCompile.Variable ℕ)
    (point : ℕ → Point) (start : ℕ) :
    ((vs.zipIdx start).filterMap fun v => match v.1 with
      | .inl (.inl _) => none
      | _ => some (f v.1, point v.2)).map Prod.fst =
        (vs.filter isAuxiliaryVariable).map f := by
  induction vs generalizing start with
  | nil => rfl
  | cons v vs ih =>
    rcases v with (v | ⟨a, b⟩) | ⟨⟨a, b⟩, s⟩ <;>
      simp [List.zipIdx_cons, isAuxiliaryVariable, ih] <;> rfl

/-- The actual fresh-position table lists exactly the mapped private profile variables. -/
theorem positiveAuxiliaryBlock_keys (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    (positiveAuxiliaryBlock φ d i c).map Prod.fst =
      ((profileVariables (clauseProfile c)).filter isAuxiliaryVariable).map
        (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c) := by
  unfold positiveAuxiliaryBlock
  exact auxiliary_block_keys (profileVariables (clauseProfile c))
    (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c)
    (fun j => positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition j) 0

/-- A single actual clause block never repeats a fresh-variable key. -/
theorem positiveAuxiliaryBlock_keys_nodup (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {i : ℕ} (hi : i < φ.length) :
    ((positiveAuxiliaryBlock φ d i φ[i]).map Prod.fst).Nodup := by
  rw [positiveAuxiliaryBlock_keys]
  apply List.Nodup.map_on
  · intro v hv w hw he
    have hv' := List.mem_filter.mp hv
    have hw' := List.mem_filter.mp hw
    exact (profileVariableMap_aux_injective φ hi hi hv'.1 hw'.1
      ((isAuxiliaryVariable_iff v).mp hv'.2) ((isAuxiliaryVariable_iff w).mp hw'.2) he).2
  · exact (CNF.nodup_distinctVars (profileFormula (clauseProfile φ[i]))).filter _

/-- Different original clause boxes have disjoint fresh-variable key lists. -/
theorem positiveAuxiliaryBlock_keys_disjoint (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {i j : ℕ} (hi : i < φ.length) (hj : j < φ.length) (hij : i ≠ j) :
    List.Disjoint ((positiveAuxiliaryBlock φ d i φ[i]).map Prod.fst)
      ((positiveAuxiliaryBlock φ d j φ[j]).map Prod.fst) := by
  rw [List.disjoint_left, positiveAuxiliaryBlock_keys, positiveAuxiliaryBlock_keys]
  intro key hki hkj
  obtain ⟨v, hv, hve⟩ := List.mem_map.mp hki
  obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hkj
  have hv' := List.mem_filter.mp hv
  have hw' := List.mem_filter.mp hw
  exact hij (profileVariableMap_aux_injective φ hi hj hv'.1 hw'.1
    ((isAuxiliaryVariable_iff v).mp hv'.2) ((isAuxiliaryVariable_iff w).mp hw'.2)
      (hve.trans hwe.symm)).1

/-- The global fresh-variable position table has no repeated key. -/
theorem positiveAuxiliaryPositions_keys_nodup (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    ((positiveAuxiliaryPositions φ d).map Prod.fst).Nodup := by
  rw [positiveAuxiliaryPositions, List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro ⟨c, i⟩ hc
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hc)
    change i < φ.length at hi
    change φ[i] = c at he
    change ((positiveAuxiliaryBlock φ d i c).map Prod.fst).Nodup
    rw [← he]
    exact positiveAuxiliaryBlock_keys_nodup φ d hi
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < φ.length := by simpa only [List.length_zipIdx] using hi
    have hj' : j < φ.length := by simpa only [List.length_zipIdx] using hj
    simpa only [Function.onFun, List.getElem_zipIdx, Nat.zero_add] using
      positiveAuxiliaryBlock_keys_disjoint φ d hi' hj' (Nat.ne_of_lt hij)

/-- No fresh position-table key can be an inherited source-variable name. -/
theorem positiveAuxiliaryPositions_ne_source (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ (positiveAuxiliaryPositions φ d).map Prod.fst) (n : ℕ) :
    v ≠ Sum.inl (Sum.inl n) := by
  rw [positiveAuxiliaryPositions, List.map_flatMap] at hv
  obtain ⟨c, _, hv⟩ := List.mem_flatMap.mp hv
  rw [positiveAuxiliaryBlock_keys] at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact profileVariableMap_aux_ne_source
    ((isAuxiliaryVariable_iff w).mp (List.mem_filter.mp hw).2) n

/-- Every actual variable position has a unique finite-table key. -/
theorem positivePositionTable_keys_nodup (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    ((positivePositionTable φ d).map Prod.fst).Nodup := by
  rw [positivePositionTable, List.map_append, List.nodup_append]
  refine ⟨?_, positiveAuxiliaryPositions_keys_nodup φ d, ?_⟩
  · simp only [positiveSourcePositions, List.map_map, Function.comp_def]
    exact (CNF.nodup_distinctVars φ).map (fun _ _ h => Sum.inl.inj (Sum.inl.inj h))
  · intro v hv w hw he
    simp only [positiveSourcePositions, List.map_map, Function.comp_def, List.mem_map] at hv
    obtain ⟨n, _, rfl⟩ := hv
    exact positiveAuxiliaryPositions_ne_source φ d hw n he.symm

/-- An actual auxiliary entry resolves to its own displayed clause-box point. -/
theorem positiveVariablePoint_auxiliary (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {v : CNF.PositiveExactOneCompile.Variable ℕ} {p : Point}
    (hm : (v, p) ∈ positiveAuxiliaryPositions φ d) : positiveVariablePoint φ d v = p :=
  positiveVariablePoint_of_mem φ d (positivePositionTable_keys_nodup φ d)
    (List.mem_append.mpr (Or.inr hm))

/-- Every actual output variable belongs to a source-clause profile with the exact global name. -/
theorem rawVariable_profile (φ : CNF ℕ) {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ (CNF.PositiveExactOneCompile.rawFormula φ).vars) :
    ∃ (c : Clause ℕ) (i : ℕ), (c, i) ∈ φ.zipIdx ∧
      ∃ w ∈ profileVariables (clauseProfile c),
        profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c w = v := by
  rw [rawFormula_eq_profiles] at hv
  obtain ⟨cl, hcl, b, hl⟩ := CNF.mem_vars.mp hv
  obtain ⟨⟨c, i⟩, hci, hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨localClause, hc, rfl⟩ := List.mem_map.mp hcl
  obtain ⟨lit, hlit, he⟩ := List.mem_map.mp hl
  refine ⟨c, i, hci, lit.1, CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr
    ⟨localClause, hc, lit.2, hlit⟩), ?_⟩
  exact congrArg Prod.fst he

/-- Every private profile variable contributes its prescribed fresh-position entry. -/
theorem positiveAuxiliaryBlock_entry (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {w : CNF.PositiveExactOneCompile.Variable ℕ}
    (hw : w ∈ profileVariables (clauseProfile c)) (ha : ∀ n, w ≠ Sum.inl (Sum.inl n)) :
    ∃ p, (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c w, p) ∈
      positiveAuxiliaryBlock φ d i c := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hw
  refine ⟨positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition j, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨(w, j), ?_, ?_⟩
  · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hj, he⟩)
  · rcases w with (n | ⟨a, b⟩) | ⟨⟨a, b⟩, s⟩
    · exact False.elim (ha n rfl)
    · rfl
    · rfl

/-- Every occurring actual output variable has a finite position-table entry. -/
theorem positivePositionTable_covers (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ (CNF.PositiveExactOneCompile.rawFormula φ).vars) :
    ∃ p, (v, p) ∈ positivePositionTable φ d := by
  obtain ⟨c, i, hci, w, hw, rfl⟩ := rawVariable_profile φ hv
  have hscope := profileVariables_scope (clauseProfile c) w hw
  rcases w with (j | ⟨a, b⟩) | ⟨⟨a, b⟩, s⟩
  · have hj : j < c.length := hscope.trans_le (profileSource_length_le c)
    have hvar : (c.getD j (0, true)).1 ∈ φ.vars := by
      apply CNF.mem_vars.mpr
      refine ⟨c, List.fst_mem_of_mem_zipIdx hci, (c.getD j (0, true)).2, ?_⟩
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    refine ⟨positiveScale • Graph.drawingPosition (SAT.incidenceGraph φ) d
      (φ.distinctVars.idxOf (c.getD j (0, true)).1) + positiveTranslation, ?_⟩
    apply List.mem_append.mpr
    apply Or.inl
    exact List.mem_map.mpr ⟨(c.getD j (0, true)).1, CNF.mem_distinctVars.mpr hvar, rfl⟩
  · obtain ⟨p, hp⟩ := positiveAuxiliaryBlock_entry φ d i c hw (by simp)
    exact ⟨p, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨(c, i), hci, hp⟩))⟩
  · obtain ⟨p, hp⟩ := positiveAuxiliaryBlock_entry φ d i c hw (by simp)
    exact ⟨p, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨(c, i), hci, hp⟩))⟩

/-- Every fresh-position record has an actual original-clause owner and a unique local profile
index. Private source placeholders are excluded from these records. -/
theorem positiveAuxiliaryPositions_origin (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {v : CNF.PositiveExactOneCompile.Variable ℕ} {p : Point}
    (hp : (v, p) ∈ positiveAuxiliaryPositions φ d) :
    ∃ (c : Clause ℕ) (i : ℕ), (c, i) ∈ φ.zipIdx ∧
      ∃ w ∈ profileVariables (clauseProfile c), (∀ n, w ≠ Sum.inl (Sum.inl n)) ∧
        v = profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c w ∧
        p = positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition
          ((profileVariables (clauseProfile c)).idxOf w) := by
  obtain ⟨⟨c, i⟩, hci, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨⟨w, j⟩, hwj, he⟩ := List.mem_filterMap.mp hp
  have hj := List.mem_zipIdx_iff_getElem?.mp hwj
  obtain ⟨hjlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  have hwm : w ∈ profileVariables (clauseProfile c) := List.fst_mem_of_mem_zipIdx hwj
  have hidx : (profileVariables (clauseProfile c)).idxOf w = j := by
    have hn := CNF.nodup_distinctVars (profileFormula (clauseProfile c))
    have h := hn.idxOf_getElem j hjlt
    change (profileVariables (clauseProfile c))[j] = w at hget
    change (profileVariables (clauseProfile c)).idxOf
      ((profileVariables (clauseProfile c))[j]) = j at h
    rwa [hget] at h
  rcases w with (n | ⟨a, b⟩) | ⟨⟨a, b⟩, s⟩
  · simp at he
  · simp only [Option.some.injEq, Prod.mk.injEq] at he
    refine ⟨c, i, hci, _, hwm, by simp, he.1.symm, ?_⟩
    simpa only [hidx] using he.2.symm
  · simp only [Option.some.injEq, Prod.mk.injEq] at he
    refine ⟨c, i, hci, _, hwm, by simp, he.1.symm, ?_⟩
    simpa only [hidx] using he.2.symm

end Cslib.Complexity.SAT.ExactOne
