/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis

/-! # Arithmetic synthesis without polynomial families

String-labelled constants need no semiring structure on the labels. Their interpretation here
is string length in the natural numbers, exercising the topic module without importing VP.
-/

open Cslib.Circuits

example : ∃ c : Circuit (arithSignature String) 0 1,
    c.size ≤ 1 ∧ ∀ x, c.eval (arithInterpretationWith String String.length) x 0 = 5 := by
  have h : Synthesis (arithInterpretationWith String String.length) (inputs 0) {fun _ => 5} 1 :=
    Synthesis.arith_const "hello"
  obtain ⟨c, hc, hs⟩ := h.exists_circuit
  exact ⟨c, hs, fun x => congrFun (hc x) 0⟩
