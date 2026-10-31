/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Tableau.Decoder.Assembly

/-!
# The decoder of the succinct tableau

The field stage is evaluated on concrete clause numbers with `decide`: one slot bit, two column
bits, one block bit, `x = [true, false]`, `n = 1` and `T = 1`, so `8` inputs and `75` gates. The
comparison chains, the borrows and carries, and the lookup of `x` give the expected values. The
constant stage depends on the noncomputable numbering of positions (`Loc.slot`), so the whole
decoder is checked through its correctness theorem instead.
-/

namespace ComplexityTests.TableauDecoder

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Tableau
open Cslib.Circuits.Boolean.Tableau.Decoder

/-- The field stage of the example. -/
private def gates : List (Op × List ℕ) := fieldGates 1 2 1 [true, false] 1 1

/-- The value of wire `w` on the clause number `idx`. -/
private def wire (idx w : ℕ) : Bool := evalOutput (List.ofFn fun i : Fin 8 => idx.testBit i) gates w

example : gates.length = 75 := by decide

-- Chain 4 compares the column `c = idx / 32 % 4` with `n = 1`; its last gate is wire `37`.
example : wire 64 37 = true ∧ wire 32 37 = false ∧ wire 96 37 = true := by decide

-- Chain 0 gives the borrows of `c - 1`: after one bit, `c % 2 = 0`.
example : wire 64 18 = true ∧ wire 32 18 = false := by decide

-- Chain 11 compares the payload `p = idx / 16` with the length `2` of `x`.
example : wire 16 (18 + 11 * 4 + 3) = true ∧ wire 32 (18 + 11 * 4 + 3) = false := by decide

-- The lookup of `x` at the payload is wire `82`: `x[0] = true` and `x[1] = false`.
example : wire 5 82 = true ∧ wire 19 82 = false := by decide

-- Every wire agrees with its intended value on these clause numbers.
example : (List.range 83).all (fun w => wire 100 w == fieldVal 1 2 1 [true, false] 1 1 100 w) :=
  by decide
example : (List.range 83).all (fun w => wire 211 w == fieldVal 1 2 1 [true, false] 1 1 211 w) :=
  by decide

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : Turing.MultiTapeTM k Bool State)

-- The decoder of any machine: its code, a linear size bound, and the bits of every clause.
example (x : List Bool) (n T : ℕ) (hn : n < 2 * T) (hx : x.length ≤ n) :
    ∃ c : Circuit signature (clauseBits k State T) (3 * (labelBits k State T + 1)),
      c.code = decoderCode tm (x, n, T) ∧
      c.size ≤ sizeConst tm * (colBits T + timeBits T + x.length + 1) ∧
      ∀ idx < 2 ^ clauseBits k State T,
        List.ofFn (c.eval interpretation fun i => idx.testBit i) =
          (clauseAt tm x n T idx).flatMap (litBits (labelBits k State T)) :=
  exists_decoder tm x hn hx

end ComplexityTests.TableauDecoder
