/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer

/-!
# The successor in binary

`encNat`, reexported from `Encodings.Nat.Bits`, encodes a natural number by its binary digits,
least significant first (`Nat.bits`).
The successor is computed by one streaming transducer whose state is the carry: on each digit `b`
in carry `c` it emits `c ^^ b` and keeps the carry `c && b`, and at the end it emits a final `1`
exactly when a carry remains. The machine reads its input once and uses no work tape.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_succ`: the successor is computable within
  `2 * (encNat n).length + 3` steps and zero work space.
* `Turing.MultiTapeTM.ComputableInLinearTimeAndSpace.natSucc`: its linear form.
-/

namespace Turing.MultiTapeTM

/-- The framed binary encoding of triples of natural numbers. -/
public abbrev encNat3 : ℕ × ℕ × ℕ ↪ List Bool := encPair encNat (encPair encNat encNat)

namespace NatSucc

/-- The successor as a transducer: the state is the carry, initially set. -/
private def succTransducer : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [c ^^ b])
  final c := if c then [true] else []
  length_step_le _ _ := by simp
  length_final_le c := by cases c <;> simp

private lemma run_succTransducer (c : Bool) (l : List Bool) :
    succTransducer.run c l = incr c l := by
  induction l generalizing c with
  | nil => cases c <;> rfl
  | cons b l ih =>
    rw [Transducer.run_cons, ih]
    cases c <;> cases b <;> simp [succTransducer, incr]

end NatSucc

open NatSucc in
/-- **Binary successor in linear time and zero work space.** One streaming transducer computes
`n + 1` from `encNat n` within `2 * (encNat n).length + 3` steps without work tapes. -/
public theorem computableInTimeAndSpace_succ :
    ComputableInTimeAndSpace (· + 1) encNat encNat (fun n => 2 * (encNat n).length + 3)
      (fun _ => 0) :=
  ⟨0, _, inferInstance, succTransducer.toTM, fun n => by
    rw [encNat_apply, encNat_apply, bits_succ, ← run_succTransducer]
    exact succTransducer.computesInTimeAndSpace_toTM n.bits⟩

/-- Binary successor in linear time and work space, from `computableInTimeAndSpace_succ`. -/
public theorem ComputableInLinearTimeAndSpace.natSucc :
    ComputableInLinearTimeAndSpace (· + 1) encNat encNat :=
  let ⟨k, Q, hQ, tm, h⟩ := computableInTimeAndSpace_succ
  ⟨3, k, Q, hQ, tm, fun n =>
    ⟨(h n).1, (h n).2.1.mono (by dsimp; omega), (h n).2.2.mono (Nat.zero_le _)⟩⟩

end Turing.MultiTapeTM
