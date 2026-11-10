/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary

/-! `growth_poly` without the modules that prove the certificate lemmas: a certificate in the
context gives no leaf, and the failure names the module to import. The import set is minimal on
purpose; `CslibFrontierTests/PolynomialGrowth.lean` checks the same certificates with the lemmas
imported. -/

open Turing.MultiTapeTM

/--
error: growth_poly: no rule or local fact bounds
  (encOut (f a)).length
by a polynomial in
  (encIn a).length
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
The certificate `hf` gives no bound: `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded_length` is not imported. Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives`.
-/
#guard_msgs in
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f encIn encOut) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encOut (f a)).length) := by
  growth_poly

-- A unary certificate names only the value lemma's module, which also provides the output length.
/--
error: growth_poly: no rule or local fact bounds
  g a
by a polynomial in
  (encIn a).length
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
The certificate `hg` gives no bound: `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded` is not imported. Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops`.
-/
#guard_msgs in
example {α : Type} {encIn : α ↪ List Bool} {g : α → ℕ}
    (hg : ComputableInPolyTime g encIn encUnary) :
    PolyBounded (fun a => (encIn a).length) (fun a => g a + 1) := by
  growth_poly

-- A certificate both in the context and passed as a hint is named once.
/--
error: growth_poly: no rule or local fact bounds
  (encOut (f a)).length
by a polynomial in
  (encIn a).length
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
The certificate `hf` gives no bound: `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded_length` is not imported. Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives`.
-/
#guard_msgs in
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f encIn encOut) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encOut (f a)).length) := by
  growth_poly [hf]

/--
error: growth_poly: no rule or local fact bounds
  (encOut (f a)).length
by a polynomial in
  (encIn a).length
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
The certificate `hf` gives no bound: `Turing.MultiTapeTM.ComputableInPolySpace.polyBounded_length` is not imported. Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain`.
-/
#guard_msgs in
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolySpace f encIn encOut) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encOut (f a)).length) := by
  growth_poly

-- `DegreeBounded.polyBounded` is in scope (`ResourceBounds` imports `ResourceBounds.Degree`).
example {α : Type} {size u : α → ℕ} (hu : DegreeBounded size u 2) :
    PolyBounded size (fun a => u a * size a) := by
  growth_poly
