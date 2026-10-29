/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.RepeatedTrials
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Clients of deterministic repetition without importing complexity-class definitions or
amplification theorems. -/

namespace ComplexityTests.RepeatedTrials

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The votes retain row order and pad the missing last bit with `false`. -/
example : repeatVotes 3 2 (fun x => x.2 == [true, false])
    (([] : List Bool), [true, false, false, true, true]) = [true, false, true] := by
  decide

/-- Extra tape bits do not contribute votes. -/
example : repeatVotes 2 1 (fun x => x.2.headD false)
    (([] : List Bool), [false, true, false, true]) = [false, true] := by
  decide

/-- Zero-width rows still produce the requested number of evaluations. -/
example : repeatVotes 3 0 (fun x => x.2.isEmpty) (([] : List Bool), [true]) =
    [true, true, true] := by
  decide

/-- With no trials, neither OR nor strict majority accepts. -/
example : repeatVotes 0 2 (fun _ => true) (([] : List Bool), [true]) = [] ∧
    repeatAny encBits 0 2 (fun _ => true) (([] : List Bool), [true]) = false ∧
    repeatMajority encBits 0 2 (fun _ => true) (([] : List Bool), [true]) = false := by
  simp only [repeatAny, repeatMajority, Polynomial.eval_zero, Polynomial.eval_ofNat]
  decide

/-- A tie rejects; two accepting votes form a strict majority. -/
example :
    repeatMajority encBits 1 1 (fun x => x.2.headD false) ([], [true, false]) = false ∧
    repeatMajority encBits 1 1 (fun x => x.2.headD false) ([], [true, true]) = true := by
  simp only [repeatMajority, Polynomial.eval_one]
  decide

/-- The full-tape equation `repeatVotes_ofFn` evaluates two 1-bit blocks. -/
example :
    repeatVotes 2 1 (fun x : Unit × List Bool => x.2.headD false)
      ((), List.ofFn (![true, false] : BitString (2 * 1))) = [true, false] := by
  rw [repeatVotes_ofFn]
  decide

/-- Polynomial-time certification composes through input-dependent dimensions. -/
example (trials width : Polynomial ℕ) :
    ComputableInPolyTime (fun x : List Bool × List Bool =>
      repeatVotes (trials.eval x.1.length) (width.eval x.1.length)
        (fun z => z.2.headD false) x) (encPair encBits encBits) encBits := by
  apply computableInPolyTime_repeatVotes <;> fun_prop

/-- The existing aggregation certificates are available without BPP or RP. -/
example {α : Type} {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (trials width : Polynomial ℕ) :
    ComputableInPolyTime (repeatAny enc trials width V) (encPair enc encBits) encBool ∧
    ComputableInPolyTime (repeatMajority enc trials width V) (encPair enc encBits) encBool :=
  ⟨computableInPolyTime_repeatAny hV _ _, computableInPolyTime_repeatMajority hV _ _⟩

end ComplexityTests.RepeatedTrials
