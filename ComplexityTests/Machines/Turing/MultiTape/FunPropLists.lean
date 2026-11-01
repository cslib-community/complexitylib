/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of local-only files)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Assembling programs with `fun_prop`

Programs stated directly, assembled by `fun_prop`, with their bounds checked once. The zero test
stays linear on a decidable condition, so an `if` on `n = 0` needs no quadratic charge for it.
-/

namespace ComplexityTests.FunPropLists

open Turing.MultiTapeTM

/-- A list operation with a test on the list, by the `isEmpty'` and `headD'` rules. -/
example : ComputableInO (fun l : List ℕ => if l.isEmpty then [] else l.headD 0 :: l.tail)
    (encList encNat) (encList encNat) (fun l => (encList encNat l).length)
    fun l => (encList encNat l).length := by
  refine .mono (by fun_prop) 16 (fun l => ?_) fun l => ?_ <;>
  · cases l with
    | nil => simp
    | cons a l =>
      simp only [encList_cons, List.length_append, length_frame, List.isEmpty_cons, List.headD_cons,
        List.tail_cons, Bool.false_eq_true, ↓reduceIte, length_encPair]
      omega

/-- Connectives and a test against a constant of a finite type, within the bounds of the pair. -/
example : ComputableInO (fun p : Bool × Bool => !(p.1 && decide (p.2 = true)) || p.2)
    (encPair encBool encBool) encBool (fun p => (encPair encBool encBool p).length)
    fun p => (encPair encBool encBool p).length :=
  .mono (by fun_prop) 8 (fun _ => by omega) fun _ => by omega

/-- `iteDecide` with `natIsZero'`: the test on `n = 0` costs no more than reading `n`. -/
example : ComputableInO (fun n => if n = 0 then 1 else n - 1) encNat encNat
    (fun n => ((encNat n).length + 1) ^ 2) fun n => (encNat n).length + 1 := by
  refine .mono (by fun_prop) 8 (fun n => ?_) fun n => ?_ <;>
  · split_ifs <;> nlinarith

/-- `optionIsNone` and `optionGetD` on a computed option. -/
example : ComputableInO (fun o : Option Bool => o.isNone || o.getD true)
    (encOption encBool) encBool (fun o => (encOption encBool o).length)
    fun o => (encOption encBool o).length :=
  .mono (by fun_prop) 4 (fun _ => by omega) fun _ => by omega

end ComplexityTests.FunPropLists
