/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Quantitative encoding clients

The encoding transport and unary exponential certificates require only the quantitative machine
API, independently of complexity classes and the padding argument.
-/

open Turing.MultiTapeTM

namespace ComplexityTests.QuantitativeEncoding

-- An arbitrary embedding reuses the same bit-word machine and evaluates its bounds on the word.
example {α β : Type} {encOut : β ↪ List Bool} {f : List Bool → β} {T S : List Bool → ℕ}
    (h : ComputableInO f encBits encOut T S) (enc : α ↪ List Bool) :
    ComputableInO (fun a => f (enc a)) enc encOut (fun a => T (enc a))
      (fun a => S (enc a)) :=
  h.comp_enc enc

-- The shared exponential certificate composes with any unary exponent producer.
example {f : List Bool → ℕ} {T S : List Bool → ℕ}
    (h : ComputableInO f encBits encUnary T S) :
    ComputableInO (fun x => 2 ^ f x) encBits encUnary
      (fun x => T x + (f x + 1) * 2 ^ f x) (fun x => S x + 2 ^ f x) :=
  ComputableInO.unary_two_pow.comp h

-- Transport the composed exponential certificate to an arbitrary input encoding.
example {α : Type} (enc : α ↪ List Bool) {f : List Bool → ℕ} {T S : List Bool → ℕ}
    (h : ComputableInO f encBits encUnary T S) :
    ComputableInO (fun a => 2 ^ f (enc a)) enc encUnary
      (fun a => T (enc a) + (f (enc a) + 1) * 2 ^ f (enc a))
      (fun a => S (enc a) + 2 ^ f (enc a)) :=
  (ComputableInO.unary_two_pow.comp h).comp_enc enc

end ComplexityTests.QuantitativeEncoding
