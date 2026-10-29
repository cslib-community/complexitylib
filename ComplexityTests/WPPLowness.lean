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
  ⟨fun _ => -2, mem_GapP_of_polyTime (.const (-2)), fun _ => -2, .const (-2),
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

/-- An `SPP` oracle is low for `GapP`, `SPP`, `LWPP` (fixed target), `WPP` (fixed target),
`CeqP`, and `PP`. -/
example :
    (GapPWithOracle (∅ : Set (List Bool)) encBits = GapP encBits ∧
      GapPWithOracle (Set.univ : Set (List Bool)) encBits = GapP encBits) ∧
    SPPWithOracle (Set.univ : Set (List Bool)) encBits = SPP encBits ∧
    LWPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = LWPP encBits ∧
    WPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = WPP encBits ∧
    CeqPWithOracle (Set.univ : Set (List Bool)) encBits = CeqP encBits ∧
    PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits :=
  ⟨⟨GapPWithOracle_eq_GapP_of_mem_SPP empty_mem_SPP encBits,
    GapPWithOracle_eq_GapP_of_mem_SPP univ_mem_SPP encBits⟩,
   SPPWithOracle_eq_SPP_of_mem_SPP univ_mem_SPP encBits,
   LWPPWithFixedTarget_eq_LWPP_of_mem_SPP univ_mem_SPP encBits,
   WPPWithFixedTarget_eq_WPP_of_mem_SPP univ_mem_SPP encBits,
   CeqPWithOracle_eq_CeqP_of_mem_SPP univ_mem_SPP encBits,
   PPWithOracle_eq_PP_of_mem_SPP univ_mem_SPP encBits⟩

/-- An `LWPP` oracle (witnessed with target `-2`) is low for `LWPP` (fixed target),
`WPP` (fixed target), `CeqP`, and `PP`, equating the `∅` and `Set.univ` oracle classes. -/
example :
    (LWPPWithFixedTarget (∅ : Set (List Bool)) encBits =
        LWPPWithFixedTarget (Set.univ : Set (List Bool)) encBits ∧
      LWPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = LWPP encBits) ∧
    WPPWithFixedTarget (Set.univ : Set (List Bool)) encBits = WPP encBits ∧
    CeqPWithOracle (Set.univ : Set (List Bool)) encBits = CeqP encBits ∧
    PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits :=
  have h0 := LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP empty_mem_LWPP encBits
  have h1 := LWPPWithFixedTarget_eq_LWPP_of_mem_LWPP univ_mem_LWPP encBits
  ⟨⟨h0.trans h1.symm, h1⟩,
   WPPWithFixedTarget_eq_WPP_of_mem_LWPP univ_mem_LWPP encBits,
   CeqPWithOracle_eq_CeqP_of_mem_LWPP univ_mem_LWPP encBits,
   PPWithOracle_eq_PP_of_mem_LWPP univ_mem_LWPP encBits⟩

/-- A `WPP` oracle is low for `PP`, and its relativized `PP` class coincides with that of
an `SPP` oracle. -/
example :
    PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits ∧
    PPWithOracle (∅ : Set (List Bool)) encBits =
      PPWithOracle (Set.univ : Set (List Bool)) encBits :=
  have h_wpp := PPWithOracle_eq_PP_of_mem_WPP univ_mem_WPP encBits
  have h_spp := PPWithOracle_eq_PP_of_mem_SPP empty_mem_SPP encBits
  ⟨h_wpp, h_spp.trans h_wpp.symm⟩

/-- Concrete scaling simulation on the constant-one `GapPWithOracle` function over an `LWPP`
oracle with target `-2`. -/
example : ∃ S : ℕ → ℤ, ComputableInPolyTime S encUnary encIntBin ∧
    (∀ n, S n ≠ 0) ∧ (fun w : List Bool => S w.length * 1) ∈ GapP encBits :=
  exists_mul_mem_GapP_of_mem_LWPP univ_mem_LWPP
    (GapP_subset_GapPWithOracle Set.univ encBits GapP.one_mem)

/-- info: 'Cslib.Complexity.acceptWeight_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.acceptWeight_exact

end ComplexityTests.WPPLowness
