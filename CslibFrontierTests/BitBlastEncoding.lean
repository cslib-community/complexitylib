/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Arithmetic.BitBlast
import CslibFrontier.Computability.Circuit.Pi
import Mathlib.Data.ZMod.Basic

/-! # Bit-blasting an odd field with an unused code word

The three values of ZMod 3 use 00, 10 and 01. Code 11 is unused; decoding it arbitrarily
must not impose a false surjectivity requirement on the encoding.
-/

open Cslib Cslib.Circuits

private def enc3 (a : ZMod 3) : BitString 2 := ![decide (a = 1), decide (a = 2)]
private def dec3 (b : BitString 2) : ZMod 3 := if b 0 then 1 else if b 1 then 2 else 0

private theorem dec3_enc3 : Function.LeftInverse dec3 enc3 := by decide

example : ¬ ∃ a, enc3 a = ![true, true] := by decide

example : dec3 ![true, true] = 1 := rfl

private def ternaryAdd : Circuit (arithSignature (ZMod 3)) 2 1 :=
  Circuit.oneGate ArithOp.add id

-- This is synthesis from already-available, valid encoded field inputs. It does not
-- identify arbitrary pairs of free bits with field elements.
example (φ : Fin 2 → (Fin 1 → Bool) → ZMod 3) :
    Synthesis Boolean.interpretation
      (Set.range fun ij : Fin 2 × Fin 2 => bitsOf enc3 (φ ij.1) ij.2)
      (Set.range fun oj : Fin 1 × Fin 2 =>
        bitsOf enc3 (fun x => φ 0 x + φ 1 x) oj.2)
      (bitBlastCost 2) := by
  have h := Synthesis.bitBlast_arithmetic
    (s := Set.range fun ij : Fin 2 × Fin 2 => bitsOf enc3 (φ ij.1) ij.2)
    enc3 dec3 dec3_enc3 ternaryAdd φ
    (fun i j => ⟨(i, j), rfl⟩)
  simpa [ternaryAdd, arithInterpretation, arithInterpretationWith] using h

-- A concrete input pair exercises reduction modulo three, with both output bits retained.
example : enc3 ((2 : ZMod 3) + 2) = ![true, false] := by decide

-- A constant over a singleton carrier has no encoded output bits and needs no Boolean gates.
example : Synthesis Boolean.interpretation (∅ : Set (BooleanFunction 0))
    (Set.range fun oj : Fin 1 × Fin 0 =>
      bitsOf (fun _ : Unit => (Fin.elim0 : BitString 0)) (fun _ => ()) oj.2) 0 := by
  let c : Circuit (fullSignature 2 Unit) 0 1 :=
    Circuit.oneGate (FullOp.con ()) Fin.elim0
  have hdecode : Function.LeftInverse (fun _ : BitString 0 => ())
      (fun _ : Unit => (Fin.elim0 : BitString 0)) := by
    intro a
    cases a
    rfl
  have h := Synthesis.bitBlast (s := (∅ : Set (BooleanFunction 0)))
    (fun _ : Unit => (Fin.elim0 : BitString 0)) (fun _ => ()) hdecode c
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa [c, bitBlastCost] using h
