/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.OfFn
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Deterministic computations on repeated random-tape blocks

Split a supplied bit list into fixed-width rows and collect one Boolean vote per row. Callers
can compute the dimensions from the encoded instance length. Missing bits read as `false`;
extra bits are ignored, and zero-width rows are retained. No probability distribution or
complexity-class error condition is imposed here.

`repeatAny` and `repeatMajority` aggregate the same votes. Their error bounds belong to the
class-specific amplification modules. `Complexity.Computability.Probabilistic.Repeat` provides
the separate probabilistic-program interface for independently sampled runs.

## Main definitions

* `Cslib.Complexity.repeatVotes`: collect the ordered votes.
* `Cslib.Complexity.repeatAny`: accept if any vote is `true`.
* `Cslib.Complexity.repeatMajority`: accept if more than half of `2 r(n)` votes are `true`.

## Main results

* `Cslib.Complexity.repeatVotes_ofFn`: votes on a full tape agree with finite block evaluation.
* `Cslib.Complexity.computableInPolyTime_repeatVotes`: producing votes takes polynomial time.
* `Cslib.Complexity.computableInPolyTime_repeatAny`,
  `Cslib.Complexity.computableInPolyTime_repeatMajority`: efficient aggregation.

## References

Extracted from the deterministic repetition implementations in `BPP.Amplification` and `RP` by
Samuel Schlesinger. For their use in error reduction, see
[S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 7][AroraBarak09].
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- Collect votes on fixed-width rows of a supplied random tape, padding missing bits with
`false` and ignoring bits beyond the prescribed rows. Zero-width rows still contribute votes. -/
def repeatVotes (trials width : ℕ) (V : α × List Bool → Bool)
    (input : α × List Bool) : List Bool :=
  (BitString.listRows trials width input.2).map (fun row => V (input.1, row))

/-- Repetition produces one vote for each prescribed trial, even on a short tape. -/
@[simp]
theorem length_repeatVotes (trials width : ℕ) (V : α × List Bool → Bool)
    (input : α × List Bool) : (repeatVotes trials width V input).length = trials := by
  simp [repeatVotes]

/-- On a full tape, votes are evaluations on its finite blocks, in order. -/
theorem repeatVotes_ofFn {trials width : ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (trials * width)) :
    repeatVotes trials width V (a, List.ofFn x) =
      List.ofFn (fun i => V (a, List.ofFn (BitString.block x i))) := by
  simp [repeatVotes, BitString.listRows_ofFn, List.map_ofFn, Function.comp_def]

/-- Producing votes takes polynomial time when the verifier and the unary dimensions do.
The dimensions may depend on the complete input, and output uses the raw bit-list encoding. -/
@[fun_prop]
theorem computableInPolyTime_repeatVotes {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} {trials width : α × List Bool → ℕ}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (htrials : ComputableInPolyTime trials (encPair enc encBits) encUnary)
    (hwidth : ComputableInPolyTime width (encPair enc encBits) encUnary) :
    ComputableInPolyTime (fun input => repeatVotes (trials input) (width input) V input)
      (encPair enc encBits) encBits := by
  unfold repeatVotes
  fun_prop

/-- The strict majority of `2 r(n)` runs of `V`, where `n` is the length of the encoded instance:
the random string is cut into `2 r(n)` rows of `p(n)` bits (`Cslib.BitString.listRows`), `V` runs
on each row, and the answer is `true` when more than `r(n)` runs accept. Bits missing from a short
random string read as `false`. -/
def repeatMajority (enc : α ↪ List Bool) (r p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  decide (r.eval (enc x.1).length <
    (repeatVotes (2 * r.eval (enc x.1).length) (p.eval (enc x.1).length) V x).countP id)

variable {enc : α ↪ List Bool}

/-- Majority votes of a polynomial-time decider take polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_repeatMajority {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (r p : Polynomial ℕ) :
    ComputableInPolyTime (repeatMajority enc r p V) (encPair enc encBits) encBool := by
  have hV' := hV
  have hvotes : ComputableInPolyTime
      (fun x => repeatVotes (2 * r.eval (enc x.1).length) (p.eval (enc x.1).length) V x)
      (encPair enc encBits) encBits :=
    (computableInPolyTime_repeatVotes hV (by fun_prop) (by fun_prop))
  unfold repeatMajority
  fun_prop

/-- On a random string of `2 r(n)` rows of `p(n)` bits, the majority vote compares the number of
accepting rows with `r(n)`. -/
theorem repeatMajority_ofFn {r p : Polynomial ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (2 * r.eval (enc a).length * p.eval (enc a).length)) :
    repeatMajority enc r p V (a, List.ofFn x) = decide (r.eval (enc a).length <
      (univ.filter fun i => V (a, List.ofFn (BitString.block x i)) = true).card) := by
  rw [repeatMajority, repeatVotes_ofFn, List.countP_ofFn, card_filter]
  rfl

/-- The disjunction of `q(n)` runs of `V`, where `n` is the length of the encoded instance: the
random string is cut into `q(n)` rows of `p(n)` bits (`Cslib.BitString.listRows`), `V` runs on each
row, and the answer is `true` when some run accepts. Bits missing from a short random string read
as `false`. -/
def repeatAny (enc : α ↪ List Bool) (q p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  (repeatVotes (q.eval (enc x.1).length) (p.eval (enc x.1).length) V x).any id

variable {enc : α ↪ List Bool}

/-- Repeating a polynomial-time decider takes polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_repeatAny {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (q p : Polynomial ℕ) :
    ComputableInPolyTime (repeatAny enc q p V) (encPair enc encBits) encBool := by
  have hV' := hV
  have hvotes : ComputableInPolyTime
      (fun x => repeatVotes (q.eval (enc x.1).length) (p.eval (enc x.1).length) V x)
      (encPair enc encBits) encBits :=
    (computableInPolyTime_repeatVotes hV (by fun_prop) (by fun_prop))
  unfold repeatAny
  fun_prop

/-- On a random string of `q(n)` rows of `p(n)` bits, the repetition accepts when some row is
accepted. -/
theorem repeatAny_ofFn_eq_true_iff {q p : Polynomial ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (q.eval (enc a).length * p.eval (enc a).length)) :
    repeatAny enc q p V (a, List.ofFn x) = true ↔
      ∃ i, V (a, List.ofFn (BitString.block x i)) = true := by
  simp [repeatAny, repeatVotes_ofFn, List.any_eq_true, List.mem_ofFn]

end Cslib.Complexity
