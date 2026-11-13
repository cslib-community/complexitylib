/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Problems.SharpCycle

/-!
# #CYCLE tests

Boundary checks for simple directed cycles (self-loops, rotations, undeclared vertices), the
empty graph, and the headline statements of Arora–Barak Theorem 9.4.
-/

namespace CslibFrontierTests.SharpCycle

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Simple cycles -/

/-- A self-loop is a simple cycle of length one. -/
example : (⟨[0], [(0, 0)]⟩ : Graph).IsSimpleCycle ([0] : Cycle ℕ) := by
  simp [Graph.isSimpleCycle_coe]

/-- Without the self-loop, a single vertex is not a cycle. -/
example : ¬ (⟨[0], []⟩ : Graph).IsSimpleCycle ([0] : Cycle ℕ) := by
  simp [Graph.isSimpleCycle_coe]

/-- Two arcs in opposite directions form one cycle; its two rotations are the same cycle. -/
example : (⟨[0, 1], [(0, 1), (1, 0)]⟩ : Graph).IsSimpleCycle ([0, 1] : Cycle ℕ) ∧
    ([0, 1] : Cycle ℕ) = ([1, 0] : Cycle ℕ) := by
  refine ⟨by simp [Graph.isSimpleCycle_coe], Cycle.coe_eq_coe.2 ⟨1, rfl⟩⟩

/-- A cycle through an undeclared vertex does not count. -/
example : ¬ (⟨[0], [(0, 1), (1, 0)]⟩ : Graph).IsSimpleCycle ([0, 1] : Cycle ℕ) := by
  simp [Graph.isSimpleCycle_coe]

/-- The empty graph has no simple cycles. -/
example : SharpCycle ⟨[], []⟩ = 0 := by
  refine (Set.ncard_eq_zero (SharpCycle.finite_setOf_isSimpleCycle _)).2
    (Set.eq_empty_iff_forall_notMem.2 fun c hc => ?_)
  induction c using Quotient.inductionOn' with
  | h p =>
    obtain ⟨hne, -, hv, -⟩ := Graph.isSimpleCycle_coe.1 hc
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    simpa using hv a List.mem_cons_self

/-! ### Theorem 9.4 -/

example (G : Graph) : {c : Cycle ℕ | G.IsSimpleCycle c}.Finite :=
  SharpCycle.finite_setOf_isSimpleCycle G

example (G : Graph) : G ∈ DirHamCycle ↔
    2 ^ (SharpCycle.layers G * G.distinctVertices.length) ≤ SharpCycle (SharpCycle.reduce G) :=
  SharpCycle.mem_DirHamCycle_iff G

example : ComputableInPolyTime SharpCycle.reduce encGraph encGraph := by
  fun_prop

example (h : ComputableInPolyTime SharpCycle encGraph encNat) : DirHamCycle ∈ P encGraph :=
  SharpCycle.DirHamCycle_mem_P h

example (h : ComputableInPolyTime SharpCycle encGraph encNat) : P encCNF = NP encCNF :=
  P_eq_NP_of_computableInPolyTime_SharpCycle h encCNF

end CslibFrontierTests.SharpCycle
