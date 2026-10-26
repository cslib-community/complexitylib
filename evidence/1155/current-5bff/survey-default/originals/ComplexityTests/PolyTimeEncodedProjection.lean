/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime

/-!
# Encoding-aware plain projections

The input context and both source encodings are fixed by the pair certificate before the
conversion is sought. These clients also check a framed-word projection inside a bit operation.
-/

open Turing.MultiTapeTM

example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {input : γ ↪ List Bool} {output : α ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f input (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encA output) :
    ComputableInPolyTime (fun x => (f x).1) input output := by
  fail_if_success (clear h; fun_prop)
  exact hf.fstWithEncoding h

example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {input : γ ↪ List Bool} {output : β ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f input (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encB output) :
    ComputableInPolyTime (fun x => (f x).2) input output := by
  fail_if_success (clear hf; fun_prop)
  exact hf.sndWithEncoding h

-- The conversion is an ordinary supplied certificate; no change of the input encoding is hidden.
example : ComputableInPolyTime
    (fun p : List Bool × ℕ => p.1.take (p.2 + 1))
    (encPair (encList encBool) encUnary) encBits := by
  have hconvert : ComputableInPolyTime (fun l => l) (encList encBool) encBits :=
    .of_tidy ComputableTidilyInPolyTime.listToBits
  fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × List Bool => p.2.take (p.1 + 1))
    (encPair encUnary (encList encBool)) encBits := by
  have hconvert : ComputableInPolyTime (fun l => l) (encList encBool) encBits :=
    .of_tidy ComputableTidilyInPolyTime.listToBits
  fun_prop
