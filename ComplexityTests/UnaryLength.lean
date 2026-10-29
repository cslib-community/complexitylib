/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-! Unary word length and exponential padding use only quantitative machine rules. -/

open Turing.MultiTapeTM

example : ComputableInO (fun l : List Bool => l.length) encBits encUnary
    (fun l => l.length) fun l => l.length :=
  ComputableInO.lengthUnary

example : ComputableInO (fun l : List Bool => 2 ^ l.length) encBits encUnary
    (fun l => l.length + (l.length + 1) * 2 ^ l.length)
    (fun l => l.length + 2 ^ l.length) :=
  ComputableInO.unary_two_pow.comp ComputableInO.lengthUnary
