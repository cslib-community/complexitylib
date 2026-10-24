/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.WPP.Bounded
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Nonvacuous clients for uniform bounded wide-gap closure, including varying bounds at a
fixed length and signed length-only targets. -/

@[expose] public section

open Cslib.Complexity Turing.MultiTapeTM

namespace WPPBoundedTests

def bitLanguage : Set (List Bool × ℕ) := {x | x.1.getD x.2 false = true}

def target (n : ℕ) : ℤ := -((n + 1 : ℕ) : ℤ)

def bound (w : List Bool) : ℕ := if w.getD 0 false then w.length else 0

@[fun_prop]
theorem target_polyTime : ComputableTidilyInPolyTime target encUnary encIntBin := by
  have hs : ComputableTidilyInPolyTime (fun n : ℕ => n + 1) encUnary encUnary := by fun_prop
  exact ComputableTidilyInPolyTime.intBin_neg.comp
    (ComputableTidilyInPolyTime.intBin_natCast.comp
      (ComputableTidilyInPolyTime.unary_to_binary.comp hs))

theorem target_ne_zero (n : ℕ) : target n ≠ 0 := by
  dsimp [target]
  lia

theorem bound_polyTime : ComputableTidilyInPolyTime bound encBits encUnary := by
  unfold bound
  fun_prop

theorem joint_mem_LWPP : bitLanguage ∈ LWPP (encPair encBits encUnary) := by
  let g (x : List Bool × ℕ) : ℤ :=
    if x.1.getD x.2 false then target ((encPair encBits encUnary) x).length else 0
  have hg : ComputableTidilyInPolyTime g (encPair encBits encUnary) encIntBin := by
    dsimp only [g]
    fun_prop
  refine ⟨g, mem_GapP_of_polyTime (.of_tidy hg), target, .of_tidy target_polyTime, target_ne_zero,
    ?_, ?_⟩
  · intro x
    cases h : x.1.getD x.2 false <;> simp only [g, h] <;> simp
  · intro x
    change (x.1.getD x.2 false = true) ↔ _
    cases h : x.1.getD x.2 false <;> simp only [g, h] <;>
      simp [Ne.symm (target_ne_zero _)]

example : {w | ∀ i < bound w, (w, i) ∈ bitLanguage} ∈ LWPP encBits :=
  forall_lt_mem_LWPP joint_mem_LWPP (.of_tidy bound_polyTime)

example : {w | ∃ i < bound w, (w, i) ∈ bitLanguage} ∈ LWPP encBits :=
  exists_lt_mem_LWPP joint_mem_LWPP (.of_tidy bound_polyTime)

example : {w | ∀ i < bound w, (w, i) ∈ bitLanguage} ∈ WPP encBits :=
  forall_lt_mem_WPP (LWPP_subset_WPP joint_mem_LWPP) (.of_tidy bound_polyTime)

example : {w | ∃ i < bound w, (w, i) ∈ bitLanguage} ∈ WPP encBits :=
  exists_lt_mem_WPP (LWPP_subset_WPP joint_mem_LWPP) (.of_tidy bound_polyTime)

-- Equal-length inputs have different bounds. Prefix targets also vary in sign and magnitude.
example : bound [true, false] = 2 ∧ bound [false, true] = 0 := by decide
example : ([true, false] : List Bool).length = [false, true].length := rfl
example : target 0 = -1 ∧ target 1 = -2 ∧ target 2 = -3 := by decide
example : (∏ i ∈ Finset.range 1, target (2 * 2 + 1 + i)) = -6 := by decide
example : (∏ i ∈ Finset.range 2, target (2 * 2 + 1 + i)) = 42 := by decide

-- Both closure languages are nonconstant; the universal one inspects more than the head bit.
example : ∀ i < bound [true, true], ([true, true], i) ∈ bitLanguage := by
  intro i hi
  have : i = 0 ∨ i = 1 := by
    have h : i < 2 := hi
    lia
  rcases this with rfl | rfl <;> rfl

example : ¬ ∀ i < bound [true, false], ([true, false], i) ∈ bitLanguage := by
  intro h
  have := h 1 (by decide)
  contradiction

example : ∃ i < bound [true, false], ([true, false], i) ∈ bitLanguage :=
  ⟨0, by decide, rfl⟩

example : ¬ ∃ i < bound [false, true], ([false, true], i) ∈ bitLanguage := by
  simp [bound]

-- Zero-length and zero-bound cases need no satisfiability assumption on the family.
example : ∀ i < bound [], ([], i) ∈ bitLanguage := by simp [bound]
example : ¬ ∃ i < bound [], ([], i) ∈ bitLanguage := by simp [bound]
example : {w : List Bool | ∀ i < 0, (w, i) ∈ bitLanguage} ∈ LWPP encBits :=
  forall_lt_mem_LWPP joint_mem_LWPP (.of_tidy (.const 0))
example : {w : List Bool | ∃ i < 0, (w, i) ∈ bitLanguage} ∈ LWPP encBits :=
  exists_lt_mem_LWPP joint_mem_LWPP (.of_tidy (.const 0))

/-- info: 'Cslib.Complexity.forall_lt_mem_WPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.forall_lt_mem_WPP
/-- info: 'Cslib.Complexity.exists_lt_mem_WPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.exists_lt_mem_WPP
/-- info: 'Cslib.Complexity.forall_lt_mem_LWPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.forall_lt_mem_LWPP
/-- info: 'Cslib.Complexity.exists_lt_mem_LWPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.exists_lt_mem_LWPP

end WPPBoundedTests
