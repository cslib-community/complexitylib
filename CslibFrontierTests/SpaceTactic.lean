/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Tactic.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

open Turing.MultiTapeTM

example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f g : α → ℕ}
    (hf : ComputableInSpace f enc encNat S) (hg : ComputableInSpace g enc encNat S) :
    ComputableInSpace (fun a => f a + g a + 1) enc encNat S := by space

example : ComputableInSpace (fun p : ℕ × Option ℕ => p.1 + p.2.getD 0)
    (encPair encNat (encOption encNat)) encNat
    (fun p => (encPair encNat (encOption encNat) p).length) := by space

example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (h : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun _ : α => 7) enc encNat S := by space

example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {g : α → ℕ} {f : ℕ → ℕ}
    (hg : ComputableInSpace g enc encNat S)
    (hf : ComputableInSpace f encNat encNat (fun n => (encNat n).length)) :
    ComputableInSpace (fun a => f (g a + 1)) enc encNat S := by space

-- Binary and unary output costs cannot be silently exchanged.
example : True := by
  fail_if_success
    have : ComputableInSpace (fun n : ℕ => n + 1) encNat encUnary
        (fun n => (encNat n).length) := by space
  trivial

namespace SpaceTacticRecord

structure State where
  index : ℕ
  answer : Option Bool

enc_structure encState : State where index : encNat, answer : (encOption encBool)

example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {st : α → State}
    (h : ComputableInSpace st enc encState S) :
    ComputableInSpace (fun a => State.mk ((st a).index + 1) (st a).answer)
      enc encState S := by space

-- No input-length allowance may be invented for an arbitrary budget.
example (_S : ℕ → ℕ) : True := by
  fail_if_success
    have : ComputableInSpace (fun n : ℕ => n) encNat encNat _S := by space
  trivial

end SpaceTacticRecord
