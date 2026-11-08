/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORChain

/-!
# Complement conjugacy of reversed Add/XNOR chains

Reversing operator/operand pairs and complementing both endpoints implements
inverse evaluation. These general chain identities support both native dictionary
orientations without depending on a machine model or memory layout.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

/-- Reversing and complementing a complete execution gives its inverse execution. -/
theorem eval_reverse_not {m : ℕ} (xs : List (Bool × BitVec m)) (s t : BitVec m) :
    eval xs.reverse (~~~t) = ~~~s ↔ eval xs s = t := by
  constructor
  · intro he
    have hb : backward xs t = s := by
      rw [backward_eq_not_eval_reverse, he, BitVec.not_not]
    rw [← hb, eval_backward]
  · intro he
    have hh := congrArg (fun z : BitVec m => ~~~z) (backward_eval xs s)
    rw [he, backward_eq_not_eval_reverse, BitVec.not_not] at hh
    exact hh

/-- Inverting a reversed chain is the complemented original forward execution. -/
theorem backward_reverse_not {m : ℕ} (xs : List (Bool × BitVec m)) (s : BitVec m) :
    backward xs.reverse (~~~s) = ~~~(eval xs s) := by
  rw [backward_eq_not_eval_reverse, List.reverse_reverse, BitVec.not_not]

end Cslib.Cryptanalysis.AddXNOR
