/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Mathlib.Tactic.Linarith

/-!
# Direct binary counter resource certificates

The successor, predecessor and zero test certificates here are weakenings of the streaming
transducer certificates `computableInTimeAndSpace_succ`, `computableInTimeAndSpace_pred` and
`computableInTimeAndSpace_isZero`. The carry rounds remain as the shared step of binary addition.

## Main results

* `ComputableInO.succStep`, `ComputableInO.succFinish`: shared linear carry-round certificates
  for binary addition.
* `ComputableInO.natSucc`, `ComputableInO.natPred`: binary counters within the quadratic clock
  and linear charged workspace used by their clients.
* `ComputableInO.natIsZero`: linear zero testing.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace ComputableInO

/-- One consuming carry round has linear time and charged workspace. -/
theorem succStep :
    ComputableInO (fun p : (Bool × List Bool) × Bool => NatSucc.succStep p.1 p.2)
      (encPair (encPair encBool encBits) encBool) (encPair encBool encBits)
      (fun p => (encPair (encPair encBool encBits) encBool p).length)
      (fun p => (encPair (encPair encBool encBits) encBool p).length) := by
  have hacc := fst (encPair encBool encBits) encBool
  have hb := snd (encPair encBool encBits) encBool
  have hc := hacc.fst'
  have hflag := (of_linear (.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 && q.2)).comp_linear (hc.prod hb)
  have hdig := (of_linear (.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 ^^ q.2)).comp_linear (hc.prod hb)
  exact (hflag.prod (hacc.snd'.append hdig (encOut := encBits) fun _ => rfl)).mono 5
    (fun _ => by omega) (fun _ => by omega)

/-- Appending the final carry has linear time and charged workspace. -/
theorem succFinish :
    ComputableInO NatSucc.succFinish (encPair encBool encBits) encBits
      (fun p => (encPair encBool encBits p).length)
      (fun p => (encPair encBool encBits p).length) := by
  have hc := fst encBool encBits
  have hds := snd encBool encBits
  have happ := hds.append (of_linear (.const (encMid := encBool) true)) (encOut := encBits)
    (g := fun p : Bool × List Bool => p.2 ++ [true]) fun _ => rfl
  unfold NatSucc.succFinish
  exact
    (hc.ite happ hds).mono (T' := fun p => (encPair encBool encBits p).length)
      (S' := fun p => (encPair encBool encBits p).length) 3
      (fun _ => by split_ifs <;> omega) (fun _ => by split_ifs <;> omega)

/-- Binary successor within the quadratic clock and linear charged workspace used by its
clients, weakened from the linear-time, zero-work-space transducer certificate
`computableInTimeAndSpace_succ`. -/
theorem natSucc :
    ComputableInO (· + 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) :=
  (of_linear .natSucc).mono_le (fun n => by simp only [encNat_apply]; nlinarith) fun _ => by omega

/-- Binary predecessor within the quadratic clock and linear charged workspace used by its
clients, weakened from the linear-time, zero-work-space transducer certificate
`computableInTimeAndSpace_pred`. -/
theorem natPred :
    ComputableInO (· - 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) :=
  (of_linear .natPred).mono_le (fun n => by simp only [encNat_apply]; nlinarith) fun _ => by omega

/-- Zero testing is linear in both resources, weakened from the transducer certificate
`computableInTimeAndSpace_isZero`; the output charge remains explicit. -/
theorem natIsZero :
    ComputableInO (fun n => decide (n = 0)) encNat encBool
      (fun n => (encNat n).length) (fun n => (encNat n).length) :=
  of_linear .natIsZero

end ComputableInO
end Turing.MultiTapeTM
