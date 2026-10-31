/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.FastLeaves

/-! # The leaf bounds of the native recursion: checked instances

A guarded input whose root is reached, well-formed and has the packet shape; the edge bound on
reached calls; and the resource analysis. -/

namespace ComplexityTests.FastLeaves

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
  Cslib.Complexity.CountingSimulation

/-- Two rows `0, 1` and two columns `2, 3`, joined by edges `0 : 0 → 2` and `1 : 1 → 3`. -/
def pair : ℕ × ExplicitTensorNetwork ℕ :=
  (2, ⟨2, [([0], [1, 2]), ([1], [3, 4]), ([0], [1, 1]), ([1], [1, 0])]⟩)

example : fastGuard pair = true := by decide

-- The root of a guarded input is reached, well-formed, and has the packet shape.
example : WF (root (ExplicitTensorNetwork.capPrecision (1, pair))) ∧
    PacketShape (root (ExplicitTensorNetwork.capPrecision (1, pair))) :=
  (Reach.root (mk := nativeMk)).wf_packetShape (wf_root 1 (by decide)) (packetShape_root _)

-- Reached calls have at most twice the scale in edges, on every input.
example (P : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) (x : Call)
    (hx : Reach nativeMk (root (ExplicitTensorNetwork.capPrecision (P, G))) x) :
    x.edges ≤ 2 * x.scale :=
  hx.edges_le_two_mul_scale rfl rfl

-- The resource analysis of the native recursion holds, with no remaining hypothesis.
example : FastAnalysis nativeMk := fastAnalysis_nativeMk_holds

end ComplexityTests.FastLeaves
