/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.WPP.TruthTable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-! Nonvacuous truth-table clients with varying query lengths/counts and negative targets. -/

@[expose] public section

open Turing.MultiTapeTM Cslib.Complexity

namespace ComplexityTests.WPPTruthTable

def oracle : Set (List Bool) := {w | w.getD 0 false = true}

def target (n : ℕ) : ℤ := -Int.ofNat (n + 1)

@[fun_prop]
theorem polyTime_target : ComputableTidilyInPolyTime target encUnary encIntBin :=
  ComputableTidilyInPolyTime.intBin_neg.comp
    (ComputableTidilyInPolyTime.intBin_natCast.comp
      (ComputableTidilyInPolyTime.unary_to_binary.comp
        (ComputableTidilyInPolyTime.unary_add.comp
          (ComputableTidilyInPolyTime.id'.prod (.const 1)))))

theorem target_ne_zero (n : ℕ) : target n ≠ 0 := by
  dsimp [target]
  lia

theorem oracle_mem_LWPP : oracle ∈ LWPP encBits := by
  let g (w : List Bool) : ℤ := if w.getD 0 false then target w.length else 0
  have hg : ComputableTidilyInPolyTime g encBits encIntBin := by dsimp [g]; fun_prop
  refine ⟨g, mem_GapP_of_polyTime (.of_tidy hg), target, .of_tidy polyTime_target, target_ne_zero,
    ?_, ?_⟩
  · intro w
    dsimp [g]
    split_ifs <;> simp
  · intro w
    change w.getD 0 false = true ↔ g w = target w.length
    simp only [g]
    cases w.getD 0 false <;> simp [(target_ne_zero w.length).symm]

def count (w : List Bool) : ℕ := if w.getD 0 false then w.length else 0

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
  {w | combine (w, truthTableAnswers (query ⁻¹' oracle) count w) = true}

theorem reduction : PolyTimeTruthTableReducible encBits encBits language oracle :=
  ⟨count, query, combine, .of_tidy polyTime_count, .of_tidy polyTime_query,
    .of_tidy polyTime_combine, fun _ => Iff.rfl⟩

example : language ∈ LWPP encBits := reduction.mem_LWPP oracle_mem_LWPP

example : language ∈ WPP encBits := reduction.mem_WPP (LWPP_subset_WPP oracle_mem_LWPP)

theorem joint_mem_LWPP : query ⁻¹' oracle ∈ LWPP (encPair encBits encUnary) :=
  PolyTimeReducible.mem_LWPP ⟨query, .of_tidy polyTime_query, fun _ => Iff.rfl⟩ oracle_mem_LWPP

example : language ∈ LWPP encBits :=
  truthTable_mem_LWPP joint_mem_LWPP (.of_tidy polyTime_count) (.of_tidy polyTime_combine)

example : language ∈ WPP encBits :=
  truthTable_mem_WPP (LWPP_subset_WPP joint_mem_LWPP) (.of_tidy polyTime_count)
    (.of_tidy polyTime_combine)

example : count [true, false] = 2 ∧ count [false, true] = 0 := by decide

example : (query ([true, false], 0)).length = 2 ∧
    (query ([true, false], 1)).length = 1 := by decide

example : target 2 = -3 ∧ target 1 = -2 := by decide

example : [true, false] ∈ language := by
  simp [language, truthTableAnswers, count, query, oracle, combine]

example : [true, true] ∉ language := by
  simp [language, truthTableAnswers, count, query, oracle, combine]

example : [false, true] ∉ language := by
  simp [language, truthTableAnswers, count, query, oracle, combine]

example : truthTableAnswers (query ⁻¹' oracle) count [] = [] := by
  simp [truthTableAnswers, count]

example : {w | (fun _ : List Bool × List Bool => true)
    (w, truthTableAnswers (query ⁻¹' oracle) (fun _ => 0) w) = true} ∈ LWPP encBits :=
  truthTable_mem_LWPP joint_mem_LWPP (.of_tidy (.const 0)) (.of_tidy (.const true))

example : {w | (fun x : List Bool × List Bool => x.1.getD 0 false)
    (w, truthTableAnswers (query ⁻¹' oracle) (fun _ => 0) w) = true} ∈ LWPP encBits :=
  truthTable_mem_LWPP (d := fun x => x.1.getD 0 false)
    joint_mem_LWPP (.of_tidy (.const 0)) (.of_tidy (by fun_prop))

end ComplexityTests.WPPTruthTable

/-- info: 'Cslib.Complexity.truthTable_mem_WPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.truthTable_mem_WPP

/-- info: 'Cslib.Complexity.truthTable_mem_LWPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.truthTable_mem_LWPP

/--
info: 'Cslib.Complexity.PolyTimeTruthTableReducible.mem_WPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PolyTimeTruthTableReducible.mem_WPP

/--
info: 'Cslib.Complexity.PolyTimeTruthTableReducible.mem_LWPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PolyTimeTruthTableReducible.mem_LWPP
