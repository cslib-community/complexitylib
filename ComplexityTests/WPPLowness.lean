/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.WPP.Lowness

/-! # Concrete SPP, LWPP, and WPP oracles and axiom guards for oracle lowness -/

@[expose] public section

namespace ComplexityTests.WPPLowness

open Cslib.Complexity Turing.MultiTapeTM

/-- The empty language has the zero GapP witness in `SPP`. -/
theorem empty_mem_SPP : (∅ : Set (List Bool)) ∈ SPP encBits :=
  ⟨0, GapP.zero_mem, fun _ => Or.inl rfl, fun _ => by simp⟩

/-- The universal language has the constant-one GapP witness in `SPP`. -/
theorem univ_mem_SPP : (Set.univ : Set (List Bool)) ∈ SPP encBits :=
  ⟨1, GapP.one_mem, fun _ => Or.inr rfl, fun _ => by simp⟩

/-- A non-SPP-style `LWPP` witness for the universal language with target `-2`. -/
theorem univ_mem_LWPP : (Set.univ : Set (List Bool)) ∈ LWPP encBits :=
  ⟨fun _ => -2, mem_GapP_of_polyTime (.of_tidy (.const (-2))), fun _ => -2, .const (-2),
    fun _ => by lia, fun _ => Or.inr rfl, fun _ => by simp⟩

/-- The empty language in `LWPP` with target `-2`. -/
theorem empty_mem_LWPP : (∅ : Set (List Bool)) ∈ LWPP encBits :=
  ⟨0, GapP.zero_mem, fun _ => -2, .const (-2),
    fun _ => by lia, fun _ => Or.inl rfl, fun _ => by simp⟩

/-- The universal language in `WPP` with target `-2`. -/
theorem univ_mem_WPP : (Set.univ : Set (List Bool)) ∈ WPP encBits :=
  LWPP_subset_WPP univ_mem_LWPP

/-- Both endpoint witnesses have actual instances. -/
example : ([] : List Bool) ∉ (∅ : Set (List Bool)) ∧
    ([] : List Bool) ∈ (Set.univ : Set (List Bool)) := by simp

example : GapPWithOracle (∅ : Set (List Bool)) encBits = GapP encBits :=
  GapPWithOracle_eq_GapP_of_mem_SPP empty_mem_SPP encBits

example : SPPWithOracle (Set.univ : Set (List Bool)) encBits = SPP encBits :=
  SPPWithOracle_eq_SPP_of_mem_SPP univ_mem_SPP encBits

example : LWPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = LWPP encBits :=
  LWPPWithFixedTarget_eq_LWPP_of_mem_SPP univ_mem_SPP encBits

example : WPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = WPP encBits :=
  WPPWithFixedTarget_eq_WPP_of_mem_SPP univ_mem_SPP encBits

example : CeqPWithOracle (Set.univ : Set (List Bool)) encBits = CeqP encBits :=
  CeqPWithOracle_eq_CeqP_of_mem_SPP univ_mem_SPP encBits

example : PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits :=
  PPWithOracle_eq_PP_of_mem_SPP univ_mem_SPP encBits

example : LWPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = LWPP encBits :=
  LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP univ_mem_LWPP encBits

example : WPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = WPP encBits :=
  WPPWithFixedTarget_eq_WPP_of_mem_LWPP univ_mem_LWPP encBits

example : CeqPWithOracle (Set.univ : Set (List Bool)) encBits = CeqP encBits :=
  CeqPWithOracle_eq_CeqP_of_mem_LWPP univ_mem_LWPP encBits

example : PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits :=
  PPWithOracle_eq_PP_of_mem_LWPP univ_mem_LWPP encBits

example : PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits :=
  PPWithOracle_eq_PP_of_mem_WPP univ_mem_WPP encBits

/-- Concrete scaling simulation on the constant-one `GapPWithOracle` function over an `LWPP`
oracle with target `-2`. -/
example : ∃ S : ℕ → ℤ, ComputableInPolyTime S encUnary encIntBin ∧
    (∀ n, S n ≠ 0) ∧ (fun w : List Bool => S w.length * 1) ∈ GapP encBits :=
  exists_mul_mem_GapP_of_mem_LWPP univ_mem_LWPP
    (GapP_subset_GapPWithOracle Set.univ encBits GapP.one_mem)

/-- info: 'Cslib.Complexity.acceptWeight_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.acceptWeight_exact

/-- info: 'Cslib.Complexity.GapP.generalWeightedReplay_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.generalWeightedReplay_mem

/-- info: 'Cslib.Complexity.generalWeightedReplay_eq_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.generalWeightedReplay_eq_exact

/-- info: 'Cslib.Complexity.GapPWithOracle_eq_GapP_of_mem_SPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapPWithOracle_eq_GapP_of_mem_SPP

/-- info: 'Cslib.Complexity.SPPWithOracle_eq_SPP_of_mem_SPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SPPWithOracle_eq_SPP_of_mem_SPP

/-- info: 'Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP_of_mem_SPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP_of_mem_SPP

/-- info: 'Cslib.Complexity.WPPWithFixedTarget_eq_WPP_of_mem_SPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.WPPWithFixedTarget_eq_WPP_of_mem_SPP

/-- info: 'Cslib.Complexity.CeqPWithOracle_eq_CeqP_of_mem_SPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CeqPWithOracle_eq_CeqP_of_mem_SPP

/-- info: 'Cslib.Complexity.PPWithOracle_eq_PP_of_mem_SPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPWithOracle_eq_PP_of_mem_SPP

/-- info: 'Cslib.Complexity.exists_mul_mem_GapP_of_mem_LWPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mul_mem_GapP_of_mem_LWPP

/-- info: 'Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP

/-- info: 'Cslib.Complexity.WPPWithFixedTarget_eq_WPP_of_mem_LWPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.WPPWithFixedTarget_eq_WPP_of_mem_LWPP

/-- info: 'Cslib.Complexity.CeqPWithOracle_eq_CeqP_of_mem_LWPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CeqPWithOracle_eq_CeqP_of_mem_LWPP

/-- info: 'Cslib.Complexity.PPWithOracle_eq_PP_of_mem_LWPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPWithOracle_eq_PP_of_mem_LWPP

/-- info: 'Cslib.Complexity.PPWithOracle_eq_PP_of_mem_WPP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPWithOracle_eq_PP_of_mem_WPP

end ComplexityTests.WPPLowness
