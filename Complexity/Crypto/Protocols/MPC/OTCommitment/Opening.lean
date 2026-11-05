/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment
import Mathlib.Data.List.OfFn

/-!
# Checking explicit OT commitment openings

The list checker rejects unequal lengths before comparing rows, so truncated zip operations
cannot turn a malformed opening into acceptance. Its output agrees with the existing finite
opening experiment on exact encodings. Empty openings retain the zero-call semantics: either
bit is accepted when both receiver lists are empty.

## Main definitions

* `OTCommitment.openResult`: finite opening result, with abort and rejection represented by `none`.
* `OTCommitment.openPairs`: total checker on explicit lists of choices, answers and opening pairs.

## Main results

* `OTCommitment.openPairs_ofFn`: exact refinement of the finite opening result.

This is an original implementation refinement of the existing ideal-OT commitment verifier,
not a new security definition or a simulator.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

/-- Receiver output after one opening; `none` represents either sender abort or rejection. -/
@[expose] noncomputable def openResult {k : ℕ} (choices received : Fin k → Bool)
    (submission : Option (Bool × Opening k)) : Option Bool :=
  match submission with
  | none => none
  | some (b, o) => if @decide (Accepts choices received b o) (Classical.propDecidable _) then
      some b else none

/-- Check an explicit opening. Abort or any unequal length is rejected; otherwise every pair
must have the submitted parity and match the receiver's selected bit. -/
@[expose] def openPairs (choices received : List Bool)
    (submission : Option (Bool × List (Bool × Bool))) : Option Bool :=
  submission.elim none fun (b, pairs) =>
    if choices.length == received.length && choices.length == pairs.length &&
        ((choices.zip received).zip pairs).all (fun row =>
          (row.2.1 ^^ row.2.2) == b &&
            (if row.1.1 then row.2.2 else row.2.1) == row.1.2) then
      some b else none

private theorem rows_ofFn {k : ℕ} (choices received : Fin k → Bool)
    (b : Bool) (o : Opening k) :
    (((List.ofFn choices).zip (List.ofFn received)).zip
      (List.ofFn fun i => (o i false, o i true))).all (fun row =>
        (row.2.1 ^^ row.2.2) == b &&
          (if row.1.1 then row.2.2 else row.2.1) == row.1.2) = true ↔
      Accepts choices received b o := by
  induction k with
  | zero => simp [Accepts]
  | succ k ih =>
    simp only [List.ofFn_succ, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      beq_iff_eq, ih, Accepts, Fin.forall_fin_succ]
    cases choices 0 <;> simp

/-- Encoding each finite vector by its complete list preserves the opening result exactly. -/
theorem openPairs_ofFn {k : ℕ} (choices received : Fin k → Bool)
    (submission : Option (Bool × Opening k)) :
    openPairs (List.ofFn choices) (List.ofFn received)
      (submission.map fun (b, o) => (b, List.ofFn fun i => (o i false, o i true))) =
        openResult choices received submission := by
  cases submission with
  | none => rfl
  | some s =>
    rcases s with ⟨b, o⟩
    change (if ((List.ofFn choices).length == (List.ofFn received).length &&
        (List.ofFn choices).length == (List.ofFn fun i => (o i false, o i true)).length &&
        (((List.ofFn choices).zip (List.ofFn received)).zip
          (List.ofFn fun i => (o i false, o i true))).all (fun row =>
            (row.2.1 ^^ row.2.2) == b &&
              (if row.1.1 then row.2.2 else row.2.1) == row.1.2)) then some b else none) = _
    rw [List.length_ofFn, List.length_ofFn, List.length_ofFn]
    rw [beq_self_eq_true, Bool.true_and, Bool.true_and]
    have hrows := Bool.eq_iff_iff.mpr ((rows_ofFn choices received b o).trans
      (iff_of_eq (@decide_eq_true_eq (Accepts choices received b o)
        (Classical.propDecidable _))).symm)
    rw [hrows]
    rfl

end Cslib.Crypto.Protocols.MPC.OTCommitment
