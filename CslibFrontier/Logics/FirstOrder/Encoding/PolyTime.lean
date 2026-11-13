/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# Reading encoded structures in polynomial time

Two polynomial-time primitives on the binary encoding `encStructure` of finite relational
structures: reading the truth table of a relation symbol, and checking that an input is well formed
for a vocabulary. Both are `fun_prop` rules for `Turing.MultiTapeTM.ComputableInPolyTime`, used by
the model checkers and verifiers that read encoded structures.

## Main results

* `Cslib.Logic.Vocabulary.computableInPolyTime_table`: reading a table of the input is
  polynomial-time.
* `Cslib.Logic.Vocabulary.computableInPolyTime_checkShape`: checking well-formedness is
  polynomial-time.
-/

public section

namespace Cslib.Logic.Vocabulary

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {L : FirstOrder.Language} {v : Vocabulary L} {γ : Type} {encIn : γ ↪ List Bool}

/-- Reading a table of the input is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_table (r : Σ n, L.Relations n)
    {a : γ → EncodedStructure} (ha : ComputableInPolyTime a encIn encStructure) :
    ComputableInPolyTime (fun x => v.table (a x) r) encIn encBits :=
  listGetDWithInput ((snd encUnary (encList encBits)).comp ha) (const (v.index r)) []

/-- Checking well-formedness is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_checkShape :
    ComputableInPolyTime v.checkShape encStructure encBool := by
  unfold Vocabulary.checkShape
  refine bool_and' (unary_beq' ((length_list encBits).comp (snd encUnary (encList encBits)))
    (const v.count)) (allConst _ fun i _ => unary_beq' ?_ ?_)
  · exact length_bits_comp (listGetDWithInput (snd encUnary (encList encBits))
      (const (i : ℕ)) [])
  · exact (unary_pow _).comp (fst encUnary (encList encBits))

end Cslib.Logic.Vocabulary
