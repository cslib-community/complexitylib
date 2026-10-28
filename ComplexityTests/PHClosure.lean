/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.PH.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Tests for Boolean closure of polynomial-hierarchy levels

Unequal and zero-length blocks check the concrete splitter; alternating predicates check both
quantifier polarities. Concrete polynomial-time languages instantiate closure at levels zero
and two.
-/

namespace ComplexityTests.PHClosure

open Cslib.Complexity Turing.MultiTapeTM

example : splitAlternatingBlocks [(1, 2), (0, 1), (2, 0)]
    [true, false, true, false, false, true] =
    ([true, false, true], [false, true, false]) := by decide

example : splitAlternatingBlocks [(0, 0), (0, 0)] [true] = ([], []) := by decide

example :
    Alternation true [2]
      (fun w => (splitAlternatingBlocks [(1, 1)] w).1 = [true] ∧
        (splitAlternatingBlocks [(1, 1)] w).2 = [false]) :=
  (alternation_splitAlternatingBlocks [(1, 1)] true
    (fun u => u = [true]) (fun v => v = [false])).mpr
    ⟨⟨[true], rfl, rfl⟩, ⟨[false], rfl, rfl⟩⟩

example (ps : List (Polynomial ℕ × Polynomial ℕ)) :
    ComputableInPolyTime
      (fun w : List Bool =>
        splitAlternatingBlocks (ps.map fun pq => (pq.1.eval w.length, pq.2.eval w.length)) w)
      encBits (encPair encBits encBits) :=
  computableInPolyTime_splitAlternatingBlocks ps (.encoding_length encBits) .id'

private theorem true_in_P : ({true} : Set Bool) ∈ P encBool :=
  ⟨id, ComputableInPolyTime.id', fun _ => Iff.rfl⟩

private theorem false_in_P : ({false} : Set Bool) ∈ P encBool :=
  ⟨Bool.not, ComputableInPolyTime.bool_not, fun b => by cases b <;> simp⟩

example : ({true} ∪ {false} : Set Bool) ∈ SigmaP 0 encBool :=
  union_mem_SigmaP (P_subset_SigmaP_zero true_in_P) (P_subset_SigmaP_zero false_in_P)

example : ({true} ∩ {false} : Set Bool) ∈ PiP 2 encBool :=
  inter_mem_PiP (SigmaP_subset_PiP_succ 1
    (SigmaP_subset_SigmaP_succ 0 (P_subset_SigmaP_zero true_in_P)))
    (SigmaP_subset_PiP_succ 1
      (SigmaP_subset_SigmaP_succ 0 (P_subset_SigmaP_zero false_in_P)))

end ComplexityTests.PHClosure
