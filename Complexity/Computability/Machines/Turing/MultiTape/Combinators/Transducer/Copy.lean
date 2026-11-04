/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer

/-!
# Copying states of a finite-state transducer

A state that emits each input symbol unchanged, stays in that state, and emits nothing at
end of input copies every word. This rule applies to arbitrary alphabets and state types;
it is shared by the binary predecessor and the unary-magnitude signed-integer transducers.

## Main results

* `Turing.MultiTapeTM.Transducer.run_eq_self`: a copying state preserves the input word.
-/

namespace Turing.MultiTapeTM.Transducer

/-- A transducer started in a copying state preserves every word, provided that state emits
nothing at the end of the input. -/
public theorem run_eq_self {Symbol Q : Type*} (T : Transducer Symbol Q) (q : Q)
    (hstep : ∀ a, T.step q a = (q, [a])) (hfinal : T.final q = []) (w : List Symbol) :
    T.run q w = w := by
  induction w with
  | nil => exact hfinal
  | cons a w ih => simp only [run_cons, hstep, List.singleton_append, ih]

end Turing.MultiTapeTM.Transducer
