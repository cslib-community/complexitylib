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
# Nonvacuity and axiom checks for PP truth-table and Boolean closure
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

theorem polyTime_count : ComputableTidilyInPolyTime count encBits encUnary := by
  unfold count
  fun_prop

theorem polyTime_query :
    ComputableTidilyInPolyTime query (encPair encBits encUnary) encBits := by
  unfold query
  fun_prop

theorem polyTime_combine :
    ComputableTidilyInPolyTime combine (encPair encBits encBits) encBool := by
  unfold combine
  fun_prop

def language : Set (List Bool) :=
  {w | combine (w, truthTableAnswers (query ⁻¹' headTrue) count w) = true}

theorem reduction : PolyTimeTruthTableReducible encBits encBits language headTrue :=
  ⟨count, query, combine, .of_tidy polyTime_count, .of_tidy polyTime_query,
    .of_tidy polyTime_combine, fun _ => Iff.rfl⟩

example : language ∈ PP encBits := reduction.mem_PP headTrue_mem_PP

example : language ∈ P encBits := reduction.mem_P headTrue_mem_P

example : languageᶜ ∈ PP encBits := reduction.compl_left.mem_PP headTrue_mem_PP

example : language ∈ PP encBits :=
  reduction.compl_right.mem_PP (compl_mem_PP headTrue_mem_PP)

example : languageᶜ ∈ PP encBits :=
  reduction.compl.mem_PP (compl_mem_PP headTrue_mem_PP)

example : PolyTimeTruthTableReducible encBits encBits headTrue headTrue :=
  PolyTimeTruthTableReducible.refl encBits headTrue

theorem joint_mem_PP : query ⁻¹' headTrue ∈ PP (encPair encBits encUnary) :=
  PolyTimeReducible.mem_PP ⟨query, .of_tidy polyTime_query, fun _ => Iff.rfl⟩ headTrue_mem_PP

example : language ∈ PP encBits :=
  truthTable_mem_PP joint_mem_PP (.of_tidy polyTime_count) (.of_tidy polyTime_combine)

example : {w : List Bool | ∀ i < count w, (w, i) ∈ query ⁻¹' headTrue} ∈ PP encBits :=
  forall_lt_mem_PP joint_mem_PP (.of_tidy polyTime_count)

example : {w : List Bool | ∃ i < count w, (w, i) ∈ query ⁻¹' headTrue} ∈ PP encBits :=
  exists_lt_mem_PP joint_mem_PP (.of_tidy polyTime_count)

example : headTrue ∩ secondTrue ∈ PP encBits :=
  inter_mem_PP headTrue_mem_PP secondTrue_mem_PP

example : headTrue ∪ secondTrue ∈ PP encBits :=
  union_mem_PP headTrue_mem_PP secondTrue_mem_PP

example : headTrue \ secondTrue ∈ PP encBits :=
  diff_mem_PP headTrue_mem_PP secondTrue_mem_PP

example : symmDiff headTrue secondTrue ∈ PP encBits :=
  symmDiff_mem_PP headTrue_mem_PP secondTrue_mem_PP

example : [true, false] ∈ language := by
  simp [language, truthTableAnswers, count, query, headTrue, combine]

example : [true, true] ∉ language := by
  simp [language, truthTableAnswers, count, query, headTrue, combine]

example : newmanPoly 1 2 = 12 := by decide

example : 2 * |newmanPoly 1 (-2)| ≤ newmanPoly 1 2 :=
  two_mul_abs_newmanPoly_neg_le (by omega) (by omega)

end ComplexityTests.PPTruthTable

/--
info: 'Cslib.Complexity.GapP.exists_abs_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.GapP.exists_abs_le_two_pow

/--
info: 'Cslib.Complexity.truthTable_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.truthTable_mem_PP

/--
info: 'Cslib.Complexity.PolyTimeTruthTableReducible.mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PolyTimeTruthTableReducible.mem_PP

/--
info: 'Cslib.Complexity.PolyTimeTruthTableReducible.mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PolyTimeTruthTableReducible.mem_P

/--
info: 'Cslib.Complexity.forall_lt_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.forall_lt_mem_PP

/--
info: 'Cslib.Complexity.exists_lt_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.exists_lt_mem_PP

/--
info: 'Cslib.Complexity.inter_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.inter_mem_PP

/--
info: 'Cslib.Complexity.union_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.union_mem_PP

/--
info: 'Cslib.Complexity.diff_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.diff_mem_PP

/--
info: 'Cslib.Complexity.symmDiff_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.symmDiff_mem_PP
