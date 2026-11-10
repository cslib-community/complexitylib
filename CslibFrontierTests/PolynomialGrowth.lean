/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Computability.GenericRAM.Native.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-! Ordinary-import regression tests for polynomial resource-growth automation. -/

open Turing.MultiTapeTM

section

variable {α : Type*} {size u v : α → ℕ}

example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => 7 * (u a + 1) ^ 3 + v a * (2 * size a + 5)) := by
  growth_poly

example (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.log 2 (u a + 1) + Nat.sqrt (size a * u a)) := by
  growth_poly

example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => max (u a) (v a) + (u a - v a) + u a / (v a + 1)) := by
  growth_poly

-- Substitution through a bound at another size, found in the context.
example {β : Type*} {size' v : β → ℕ} {g : α → β}
    (hv : PolyBounded size' v) (hg : PolyBounded size (fun a => size' (g a))) :
    PolyBounded size (fun a => v (g a) + size a) := by
  growth_poly

-- Substitution into a polynomially bounded function of one natural number.
example {F : ℕ → ℕ} (hF : Cslib.PolynomiallyBounded F) (hu : PolyBounded size u) :
    PolyBounded size (fun a => F (2 * u a + size a + 1)) := by
  growth_poly

-- A function of one natural number that `fun_prop` bounds, and an arithmetic definition.
example (hu : PolyBounded size u) :
    PolyBounded size (fun a => (fun n => 3 * n ^ 2 + 1) (u a) + Nat.succ (u a)) := by
  growth_poly

-- Leaves inside conjunctions; `IsPolynomial` below unfolds to one.
example (h : PolyBounded size u ∧ PolyBounded size v) :
    PolyBounded size (fun a => u a * v a + 1) := by
  growth_poly

-- A local `let` and an extra fact passed at the call.
example (h : PolyBounded size u ∧ True) : PolyBounded size (fun a => u a ^ 2) := by
  let B := fun a => u a * u a
  have : PolyBounded size B := by growth_poly
  growth_poly [h.1]

-- A variable exponent and an unknown function are deliberately unsupported.
example (_hu : PolyBounded size u) : True := by
  fail_if_success have : PolyBounded id (fun n : ℕ => 2 ^ n) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => u a ^ size a) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => Nat.factorial (u a)) := by growth_poly
  trivial

/--
error: growth_poly: no rule or local fact bounds
  (u a).factorial
by a polynomial in
  size a
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
-/
#guard_msgs in
example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => u a + v a * Nat.factorial (u a)) := by
  growth_poly

-- Failure is decided by the syntax of the bound, within a small budget.
set_option maxHeartbeats 2000 in
-- A small budget: the unbounded factorial must be rejected without search.
example (_hu : PolyBounded size u) : True := by
  let w := fun a => (u a + 1) ^ 4 * (2 * u a + 3) + (u a + size a) * (u a + 7)
  fail_if_success have : PolyBounded size (fun a => w a + Nat.factorial (size a)) := by growth_poly
  trivial

end

-- Leaves from polynomial-time certificates: the encoded output length, and a unary value.
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {g : α → ℕ}
    (hf : ComputableInPolyTime f encIn encOut) (hg : ComputableInPolyTime g encIn encUnary) :
    PolyBounded (fun a => (encIn a).length)
      (fun a => 2 * (encOut (f a)).length + g a ^ 2 + (encIn a).length) := by
  growth_poly

-- A bit-string certificate bounds the word's length, and a composed unary one its value.
example {α : Type} {encIn : α ↪ List Bool} {g : α → List Bool} {h : α → List ℕ}
    (hg : ComputableInPolyTime g encIn encBits)
    (hh : ComputableInPolyTime (List.length ∘ h) encIn encUnary) :
    PolyBounded (fun a => (encIn a).length) (fun a => (g a).length * (h a).length) := by
  growth_poly

-- A certificate composed after another one, through its output-length bound.
example {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTime f encMid encOut) (hg : ComputableInPolyTime g encIn encMid) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encOut (f (g a))).length + 1) := by
  growth_poly

-- A polynomial native certificate: its time bound from the definition of `IsPolynomial`, its
-- output length through the polynomial-time certificate it yields.
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (c : Cslib.GenericRAM.NativeCertificate f encIn encOut) (hc : c.IsPolynomial) :
    PolyBounded (fun a => (encIn a).length) (fun a => c.time a * (encOut (f a)).length) := by
  growth_poly

-- Polynomial-space and logspace certificates through their output lengths, and a degree bound.
example {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : α → β} {g : α → γ} {u : α → ℕ}
    (hf : ComputableInPolySpace f encIn encMid) (hg : ComputableInLogSpace g encIn encOut)
    (hu : DegreeBounded (fun a => (encIn a).length) u 3) :
    PolyBounded (fun a => (encIn a).length)
      (fun a => (encMid (f a)).length * (encOut (g a)).length + u a) := by
  growth_poly

-- The modules that the failure messages and the documentation name for the certificate lemmas;
-- `CslibFrontierTests/PolynomialGrowthImports.lean` checks the messages without them.
open Lean in
run_meta do
  let env ← getEnv
  let machines := `CslibFrontier.Computability.Machines.Turing.MultiTape
  for (lem, mod) in [
      (``ComputableInPolyTime.polyBounded, machines ++ `Internal.PolyTimeLoops),
      (``ComputableInPolyTime.polyBounded_length, machines ++ `Internal.PolyTimePrimitives),
      (``ComputableInPolySpace.polyBounded_length, machines ++ `Complexity.PolySpace.Plain),
      (``ComputableInLogSpace.polyBounded_length, machines ++ `Complexity.LogSpace),
      (``DegreeBounded.polyBounded, machines ++ `ResourceBounds.Degree),
      (``Cslib.GenericRAM.NativeCertificate.polyTime,
        `CslibFrontier.Computability.GenericRAM.Native.Certificate)] do
    let some i := env.getModuleIdxFor? lem | throwError "{lem} is not imported"
    let home := env.header.moduleNames[i.toNat]!
    unless home == mod do throwError "{lem} is proved in {home}, not {mod}"

example {F : ℕ → ℕ} (hF : Cslib.PolynomiallyBounded F) :
    Cslib.PolynomiallyBounded (fun n => 3 * F n ^ 2 + Nat.log 2 (n + 1)) := by
  growth_poly

-- Polynomial growth does not establish an exact word-width admission condition.
example : PolyBounded id (fun n : ℕ => n + 1) ∧ Cslib.WordRAM.Fits 3 7 ∧
    ¬Cslib.WordRAM.Fits 3 8 := by
  refine ⟨?_, by decide, by decide⟩
  growth_poly

example : True := by
  fail_if_success have : Cslib.WordRAM.Fits 3 8 := by growth_poly
  trivial
