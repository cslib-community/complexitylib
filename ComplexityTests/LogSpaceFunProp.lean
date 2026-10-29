/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-!
# Tests for `fun_prop` on logspace computability

Each certificate below is closed by a single `fun_prop`.
-/

namespace ComplexityTests.LogSpaceFunProp

open Turing.MultiTapeTM

/-- Pairs, projections and word operations. -/
example : ComputableInLogSpace (fun p : List Bool × List Bool => (p.2 ++ p.1, p.1.headD false))
    (encPair encBits encBits) (encPair encBits encBool) := by
  fun_prop

/-- A case distinction between the counter-program primitives. -/
example : ComputableInLogSpace
    (fun p : List Bool × ℕ => if p.1.headD false then p.1.take p.2 else p.1.drop p.2)
    (encPair encBits encUnary) encBits := by
  fun_prop

/-- List lookup at a computed index, with a default value. -/
example : ComputableInLogSpace (fun p : List (List Bool) × ℕ => (p.1[p.2 + p.2]?).getD [])
    (encPair (encList encBits) encUnary) encBits := by
  fun_prop

/-- Unary arithmetic and a comparison with a constant. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => decide (p.1 * 3 + p.2 ≤ 5))
    (encPair encUnary encUnary) encBool := by
  fun_prop

/-- A supplied logspace certificate composes with the registered rules. -/
example (f : List Bool → Bool) (hf : ComputableInLogSpace f encBits encBool) :
    ComputableInLogSpace (fun p : List Bool × List Bool => [f (p.1 ++ p.2), f p.2])
      (encPair encBits encBits) (encList encBool) := by
  fun_prop

/-- **The transition to polynomial time**: a polynomial-time goal about a logspace certificate. -/
example (f : List Bool → Bool) (hf : ComputableInLogSpace f encBits encBool) :
    ComputableInPolyTime (fun p : List Bool × ℕ => f (p.1.drop p.2)) (encPair encBits encUnary)
      encBool := by
  fun_prop

end ComplexityTests.LogSpaceFunProp
