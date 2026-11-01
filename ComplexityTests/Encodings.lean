/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Tests for the framed encodings
-/

namespace ComplexityTests.Encodings

open Turing.MultiTapeTM

example : frame [true, false] = [true, true, true, false, false] := rfl

example : encPair encNat encBool (2, true) = [true, false, true, true, false, true] := by
  decide

example : encList encBool [true, false] = [true, true, false, true, false, false] := rfl

example (w u : List Bool) : unframe (frame w ++ u) = w := unframe_frame_append w u

-- Binary successor can expose its raw output word with precisely the same time/space bounds.
example : ComputableInTimeAndSpace (fun n : ℕ => encNat (n + 1)) encNat encBits
    (fun n => 2 * (encNat n).length + 3) (fun _ => 0) :=
  let ⟨k, Q, hQ, tm, h⟩ := computableInTimeAndSpace_succ
  ⟨k, Q, hQ, tm, h⟩

-- The encoded successor, one digit longer after a carry out, is written within the linear clock.
example (n : ℕ) : (encNat (n + 1)).length ≤ 2 * (encNat n).length + 3 :=
  computableInTimeAndSpace_succ.length_le n

-- Binary predecessor and zero test: one transducer each, with the same exact bounds.
example : ComputableInTimeAndSpace (fun n : ℕ => encNat (n - 1)) encNat encBits
    (fun n => 2 * (encNat n).length + 3) (fun _ => 0) :=
  let ⟨k, Q, hQ, tm, h⟩ := computableInTimeAndSpace_pred
  ⟨k, Q, hQ, tm, h⟩

example : ComputableInTimeAndSpace (fun n : ℕ => encBool (decide (n = 0))) encNat encBits
    (fun n => 2 * (encNat n).length + 3) (fun _ => 0) :=
  let ⟨k, Q, hQ, tm, h⟩ := computableInTimeAndSpace_isZero
  ⟨k, Q, hQ, tm, h⟩

-- Concrete instances: the borrow out of `4 = 0b100` drops the leading digit, `0 - 1 = 0`, and the
-- clock for `4` (three digits) is `9` steps.
example : encNat (4 - 1) = [true, true] ∧ encNat (0 - 1) = [] ∧
    encNat (6 - 1) = [true, false, true] ∧ (fun n => 2 * (encNat n).length + 3) 4 = 9 := by
  decide

example : encBool (decide ((0 : ℕ) = 0)) = [true] ∧ encBool (decide ((4 : ℕ) = 0)) = [false] := by
  decide

end ComplexityTests.Encodings
