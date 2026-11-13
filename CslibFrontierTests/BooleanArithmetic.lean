/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Boolean.Arithmetic
import CslibFrontier.Computability.Circuit.Boolean.ArithmeticRing
import Mathlib.Data.ZMod.Basic
import Cslib.Computability.Circuit.Composition
import CslibFrontier.Computability.Circuit.Pi

/-! # Two-element arithmetic/Boolean circuit clients

Multiple outputs test preservation of XOR and AND together. Constant and pure-wiring clients
exercise zero inputs and a zero gate budget. Arithmetic here means evaluation in Bool's
Boolean ring, not polynomial equality.
-/

open Cslib.Circuits

private def arithmeticPair : Circuit (arithSignature Bool) 2 2 :=
  (Circuit.oneGate (σ := arithSignature Bool) ArithOp.add id).append
    (Circuit.oneGate (σ := arithSignature Bool) ArithOp.mul id)

example : ∃ d : Circuit Boolean.signature 2 2,
    d.size ≤ 8 ∧ ∀ x, d.eval Boolean.interpretation x = ![x 0 ^^ x 1, x 0 && x 1] := by
  obtain ⟨d, he, hs⟩ := Boolean.exists_boolean_simulation arithmeticPair
  refine ⟨d, ?_, ?_⟩
  · simpa [arithmeticPair] using hs
  · intro x
    rw [he]
    ext i
    fin_cases i <;> rfl

private def booleanPair : Circuit Boolean.signature 2 2 :=
  (Circuit.oneGate (σ := Boolean.signature) Boolean.Op.or id).append
    (Circuit.oneGate (σ := Boolean.signature) Boolean.Op.not (fun _ => 0))

example : ∃ d : Circuit (arithSignature Bool) 2 2,
    d.size ≤ 6 ∧ ∀ x, d.eval (arithInterpretation Bool) x = ![x 0 || x 1, !(x 0)] := by
  obtain ⟨d, he, hs⟩ := Boolean.exists_arithmetic_simulation booleanPair
  refine ⟨d, ?_, ?_⟩
  · simpa [booleanPair] using hs
  · intro x
    rw [he]
    ext i
    fin_cases i <;> rfl

example : ∃ d : Circuit (arithSignature Bool) 0 1,
    d.size ≤ 3 ∧ ∀ x, d.eval (arithInterpretation Bool) x 0 = true := by
  obtain ⟨d, he, hs⟩ := Boolean.exists_arithmetic_simulation
    (Circuit.oneGate (Boolean.Op.const true) Fin.elim0 : Circuit Boolean.signature 0 1)
  refine ⟨d, hs, ?_⟩
  intro x
  rw [he]
  rfl

example : ∃ d : Circuit Boolean.signature 0 1,
    d.size ≤ 4 ∧ ∀ x, d.eval Boolean.interpretation x 0 = false := by
  obtain ⟨d, he, hs⟩ := Boolean.exists_boolean_simulation
    (Circuit.oneGate (ArithOp.const false) Fin.elim0 : Circuit (arithSignature Bool) 0 1)
  refine ⟨d, hs, ?_⟩
  intro x
  rw [he]
  rfl

example : ∃ d : Circuit (arithSignature Bool) 2 2,
    d.size = 0 ∧ ∀ x, d.eval (arithInterpretation Bool) x = x := by
  obtain ⟨d, he, hs⟩ := Boolean.exists_arithmetic_simulation
    (Circuit.wiring Boolean.signature id : Circuit Boolean.signature 2 2)
  refine ⟨d, Nat.eq_zero_of_le_zero hs, ?_⟩
  intro x
  rw [he]
  rfl

-- The new simulation works in odd characteristic and preserves both outputs together.
example : ∃ d : Circuit (arithSignature (ZMod 3)) 2 2,
    d.size ≤ 10 ∧ ∀ x : Fin 2 → Bool,
      d.eval (arithInterpretation (ZMod 3)) (fun i => (x i).toNat) =
        ![((x 0 || x 1).toNat : ZMod 3), (!(x 0)).toNat] := by
  obtain ⟨d, hs, he⟩ := Boolean.exists_ring_simulation (R := ZMod 3) booleanPair
  refine ⟨d, ?_, ?_⟩
  · simpa [booleanPair] using hs
  · intro x
    rw [he]
    ext i
    fin_cases i <;> rfl

-- Constants require no source inputs, and both Boolean values are retained in characteristic 3.
example : ∃ d : Circuit (arithSignature (ZMod 3)) 0 2,
    d.size ≤ 10 ∧ ∀ x, d.eval (arithInterpretation (ZMod 3)) x = ![0, 1] := by
  let c : Circuit Boolean.signature 0 2 :=
    (Circuit.oneGate (Boolean.Op.const false) Fin.elim0).append
      (Circuit.oneGate (Boolean.Op.const true) Fin.elim0)
  obtain ⟨d, hs, he⟩ := Boolean.exists_ring_simulation (R := ZMod 3) c
  refine ⟨d, ?_, ?_⟩
  · simpa [c] using hs
  · intro x
    have hinput : x = (fun i : Fin 0 => ((Fin.elim0 i : Bool).toNat : ZMod 3)) :=
      funext fun i => Fin.elim0 i
    rw [hinput, he]
    ext i
    fin_cases i <;> rfl

-- The same theorem works over an infinite ring, and wiring costs no gates.
example : ∃ d : Circuit (arithSignature ℤ) 2 2,
    d.size = 0 ∧ ∀ x : Fin 2 → Bool,
      d.eval (arithInterpretation ℤ) (fun i => (x i).toNat) = fun i => ((x i).toNat : ℤ) := by
  obtain ⟨d, hs, he⟩ := Boolean.exists_ring_simulation (R := ℤ)
    (Circuit.wiring Boolean.signature id : Circuit Boolean.signature 2 2)
  exact ⟨d, Nat.eq_zero_of_le_zero hs, he⟩
