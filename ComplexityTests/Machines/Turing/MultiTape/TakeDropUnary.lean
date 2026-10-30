/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTakeDropUnary

/-! Linear-time unary take and drop on encoded lists: instances and the streaming semantics. -/

open Turing.MultiTapeTM

/-- The plain certificates instantiate on lists of unary numbers, at degree one. -/
example :
    ComputableInDegree (fun p : List ℕ × ℕ => p.1.take p.2)
      (encPair (encList encUnary) encUnary) (encList encUnary) 1 1 ∧
    ComputableInDegree (fun p : List ℕ × ℕ => p.1.drop p.2)
      (encPair (encList encUnary) encUnary) (encList encUnary) 1 1 :=
  ⟨ComputableInDegree.takeUnary encUnary, ComputableInDegree.dropUnary encUnary⟩

/-! The machine's streaming semantics on a small encoded list, including an empty element. -/

example : TakeDropUnary.stream true false 2 (encList encUnary [2, 0, 1]) =
    encList encUnary [2, 0] := by decide

example : TakeDropUnary.stream false false 2 (encList encUnary [2, 0, 1]) =
    encList encUnary [1] := by decide

example : TakeDropUnary.stream true false 5 (encList encUnary [2, 0, 1]) =
    encList encUnary [2, 0, 1] := by decide

example : TakeDropUnary.stream false false 0 (encList encUnary [2, 0, 1]) =
    encList encUnary [2, 0, 1] := by decide
