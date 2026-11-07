/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.Guarded

/-! # A contraction algorithm from a guarded fast algorithm

The hypotheses of `ContractionAlgorithm.ofGuarded` are satisfiable: with a guard that always
fails, direct summation alone is a contraction algorithm for networks of bounded size `s`. -/

namespace ComplexityTests.GuardedContraction

open Cslib.Complexity.CountingSimulation Cslib.Circuits.Frontier
  Cslib.Circuits.Frontier.ExplicitTensorNetwork Turing.MultiTapeTM

/-- Networks with at most `C s` edges and size at most `C`. -/
def Bounded (C s : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) : Prop := G.2.numEdges ≤ C * s ∧ s ≤ C

/-- Direct summation alone, behind a guard that always fails. -/
noncomputable example :
    ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction) Bounded :=
  ContractionAlgorithm.ofGuarded (guard := fun _ => false) (ComputableInPolyTime.const false)
    directContractionBinaryCertificate (fun _ _ h => absurd h (by simp))
    (fun _ _ => ⟨0, fun _ _ _ _ _ _ _ h => absurd h (by simp)⟩)
    (fun _ _ _ h => h.1) (fun C => ⟨C, fun _ _ h _ => h.2⟩)

end ComplexityTests.GuardedContraction
