/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.Certificate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial bit computation of native program literals

A fixed expression template computes binary immediate values from runtime
metadata. Lengths and exponents are unary; data words are binary. Powers of two
are constructed directly in binary from unary expressions, without building
exponentially long unary intermediate words. The generated literals, including
all intermediate arithmetic, have actual multitape polynomial time/space
certificates. No execution or compiler oracle is an input.
-/

public section

namespace Cslib.WordRAM.ProgramLiterals

open Turing.MultiTapeTM Cslib.GenericRAM

/-- Unary size parameters and binary data-word parameters. -/
abbrev Input (u v : ℕ) := (Fin u → ℕ) × (Fin v → ℕ)

/-- Widths/lengths are unary; word-valued parameters remain binary. -/
noncomputable abbrev encoding (u v : ℕ) : Input u v ↪ List Bool :=
  encPair (encPi encUnary) (encPi encNat)

/-- Unary expressions for lengths and exponents. -/
inductive Unary (u : ℕ) where
  | literal (n : ℕ)
  | parameter (i : Fin u)
  | add (a b : Unary u)

/-- Evaluate unary metadata without exponential unary intermediates. -/
def Unary.eval {u v : ℕ} : Unary u → Input u v → ℕ
  | .literal n, _ => n
  | .parameter i, x => x.1 i
  | .add a b, x => a.eval x + b.eval x

/-- Every fixed unary metadata expression is a concrete polynomial bit computation. -/
theorem Unary.polyTime {u v : ℕ} (e : Unary u) :
    ComputableInPolyTime (e.eval (v := v)) (encoding u v) encUnary := by
  induction e with
  | literal n => exact .const n
  | parameter i => change ComputableInPolyTime (fun x : Input _ _ => x.1 i) _ _; fun_prop
  | add a b ha hb => exact ComputableInPolyTime.unary_add.comp (ha.prod hb)

/-- Binary expressions, with powers restricted to unary metadata exponents. -/
inductive Expr (u v : ℕ) where
  | literal (n : ℕ)
  | parameter (i : Fin v)
  | unary (n : Unary u)
  | powTwo (n : Unary u)
  | add (a b : Expr u v)
  | sub (a b : Expr u v)
  | mul (a b : Expr u v)
  | div (a b : Expr u v)
  | mod (a b : Expr u v)
  | xor (a b : Expr u v)

/-- Ordinary natural arithmetic, matching the unsigned standard word-RAM literal semantics. -/
def Expr.eval {u v : ℕ} : Expr u v → Input u v → ℕ
  | .literal n, _ => n
  | .parameter i, x => x.2 i
  | .unary n, x => n.eval x
  | .powTwo n, x => 2 ^ n.eval x
  | .add a b, x => a.eval x + b.eval x
  | .sub a b, x => a.eval x - b.eval x
  | .mul a b, x => a.eval x * b.eval x
  | .div a b, x => a.eval x / b.eval x
  | .mod a b, x => a.eval x % b.eval x
  | .xor a b, x => a.eval x ^^^ b.eval x

/-- Actual binary arithmetic and direct unary-exponent powers give polynomial generation. -/
theorem Expr.polyTime {u v : ℕ} (e : Expr u v) :
    ComputableInPolyTime e.eval (encoding u v) encNat := by
  induction e with
  | literal n => exact .const n
  | parameter i => change ComputableInPolyTime (fun x : Input _ _ => x.2 i) _ _; fun_prop
  | unary n => exact ComputableInPolyTime.unary_to_binary.comp n.polyTime
  | powTwo n => exact ComputableInPolyTime.binary_two_pow.comp n.polyTime
  | add a b ha hb => exact ComputableInPolyTime.binary_add.comp (ha.prod hb)
  | sub a b ha hb => exact ComputableInPolyTime.binary_sub.comp (ha.prod hb)
  | mul a b ha hb => exact ComputableInPolyTime.binary_mul' ha hb
  | div a b ha hb => exact ComputableInPolyTime.binary_div.comp (ha.prod hb)
  | mod a b ha hb => exact ComputableInPolyTime.binary_mod.comp (ha.prod hb)
  | xor a b ha hb => exact ComputableInPolyTime.binary_xor.comp (ha.prod hb)

/-- Evaluate a fixed list of literal templates in instruction order. -/
def evaluate {u v : ℕ} (es : List (Expr u v)) (x : Input u v) : List ℕ :=
  es.map (fun e => e.eval x)

/-- Literal-list construction is computed and charged, including every binary output value. -/
theorem evaluate_polyTime {u v : ℕ} (es : List (Expr u v)) :
    ComputableInPolyTime (evaluate es) (encoding u v) (encList encNat) := by
  induction es with
  | nil => exact .const []
  | cons e es ih =>
    have he := e.polyTime
    change ComputableInPolyTime (fun x => e.eval x :: evaluate es x) _ _
    fun_prop

/-- One implementing finite machine with charged time and simultaneous workspace profiles. -/
noncomputable def evaluateCertificate {u v : ℕ} (es : List (Expr u v)) :
    NativeCertificate (evaluate es) (encoding u v) (encList encNat) :=
  .ofPolyTime (evaluate_polyTime es)

/-- Both profiles are polynomial in the actual mixed unary/binary metadata encoding length. -/
theorem evaluateCertificate_isPolynomial {u v : ℕ} (es : List (Expr u v)) :
    (evaluateCertificate es).IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial (evaluate_polyTime es)

end Cslib.WordRAM.ProgramLiterals
