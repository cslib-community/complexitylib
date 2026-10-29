/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP.TruthTable
import Complexity.Computability.Complexity.Classes.PP.Closure
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Nonvacuity checks for PP truth-table and Boolean closure
-/

@[expose] public section

open Turing.MultiTapeTM Cslib.Complexity

namespace ComplexityTests.PPTruthTable

def headTrue : Set (List Bool) := {w | w.getD 0 false = true}

def secondTrue : Set (List Bool) := {w | w.getD 1 false = true}

theorem headTrue_mem_P : headTrue ∈ P encBits :=
  ⟨fun w => w.getD 0 false, by fun_prop, fun _ => Iff.rfl⟩

theorem secondTrue_mem_P : secondTrue ∈ P encBits :=
  ⟨fun w => w.getD 1 false, by fun_prop, fun _ => Iff.rfl⟩

theorem headTrue_mem_PP : headTrue ∈ PP encBits :=
  NP_subset_PP (P_subset_NP headTrue_mem_P)

theorem secondTrue_mem_PP : secondTrue ∈ PP encBits :=
  NP_subset_PP (P_subset_NP secondTrue_mem_P)

def count (w : List Bool) : ℕ := w.length

def query (x : List Bool × ℕ) : List Bool := x.1.drop x.2

def combine (x : List Bool × List Bool) : Bool :=
  x.2.getD 0 false ^^ x.2.getD 1 false

theorem polyTime_count : ComputableInPolyTime count encBits encUnary := by
  unfold count
  fun_prop

theorem polyTime_query :
    ComputableInPolyTime query (encPair encBits encUnary) encBits := by
  unfold query
  fun_prop

theorem polyTime_combine :
    ComputableInPolyTime combine (encPair encBits encBits) encBool := by
  unfold combine
  fun_prop

def language : Set (List Bool) :=
  {w | combine (w, truthTableAnswers (query ⁻¹' headTrue) count w) = true}

theorem reduction : PolyTimeTruthTableReducible encBits encBits language headTrue :=
  ⟨count, query, combine, polyTime_count, polyTime_query, polyTime_combine, fun _ => Iff.rfl⟩

theorem joint_mem_PP : query ⁻¹' headTrue ∈ PP (encPair encBits encUnary) :=
  PolyTimeReducible.mem_PP ⟨query, polyTime_query, fun _ => Iff.rfl⟩ headTrue_mem_PP

/-- Truth-table reductions preserve `PP` and `P` membership, including under left, right, and
two-sided complementation. -/
example :
    (language ∈ PP encBits ∧ language ∈ P encBits ∧ languageᶜ ∈ PP encBits) ∧
    (language ∈ PP encBits ∧ languageᶜ ∈ PP encBits ∧ headTrueᶜ ∈ PP encBits) :=
  ⟨⟨reduction.mem_PP headTrue_mem_PP,
    reduction.mem_P headTrue_mem_P,
    reduction.compl_left.mem_PP headTrue_mem_PP⟩,
   ⟨reduction.compl_right.mem_PP (compl_mem_PP headTrue_mem_PP),
    reduction.compl.mem_PP (compl_mem_PP headTrue_mem_PP),
    (PolyTimeTruthTableReducible.refl encBits headTrue).compl_left.mem_PP headTrue_mem_PP⟩⟩

/-- Direct truth-table, bounded-quantifier, and Boolean closures in `PP`. -/
example :
    (language ∈ PP encBits ∧
      {w : List Bool | ∀ i < count w, (w, i) ∈ query ⁻¹' headTrue} ∈ PP encBits ∧
      {w : List Bool | ∃ i < count w, (w, i) ∈ query ⁻¹' headTrue} ∈ PP encBits) ∧
    (headTrue ∩ secondTrue ∈ PP encBits ∧
      headTrue ∪ secondTrue ∈ PP encBits ∧
      headTrue \ secondTrue ∈ PP encBits ∧
      symmDiff headTrue secondTrue ∈ PP encBits) :=
  ⟨⟨truthTable_mem_PP joint_mem_PP polyTime_count polyTime_combine,
    forall_lt_mem_PP joint_mem_PP polyTime_count,
    exists_lt_mem_PP joint_mem_PP polyTime_count⟩,
   ⟨inter_mem_PP headTrue_mem_PP secondTrue_mem_PP,
    union_mem_PP headTrue_mem_PP secondTrue_mem_PP,
    diff_mem_PP headTrue_mem_PP secondTrue_mem_PP,
    symmDiff_mem_PP headTrue_mem_PP secondTrue_mem_PP⟩⟩

example : [true, false] ∈ language := by
  simp [language, truthTableAnswers, count, query, headTrue, combine]

example : [true, true] ∉ language := by
  simp [language, truthTableAnswers, count, query, headTrue, combine]

example : newmanPoly 1 2 = 12 ∧ 2 * |newmanPoly 1 (-2)| ≤ 12 := by
  have hval : newmanPoly 1 2 = 12 := by decide
  exact ⟨hval, hval ▸ two_mul_abs_newmanPoly_neg_le (by omega) (by omega)⟩

end ComplexityTests.PPTruthTable
