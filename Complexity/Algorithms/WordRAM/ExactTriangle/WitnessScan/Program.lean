/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Native original-weight verification in one vertex interval

The program reads the original canonical-signed A–B, B–C and A–C arrays, tests each vertex
in the supplied interval using two actual signed-addition kernels, and returns a flag and
an original vertex witnessing a zero sum. It writes no memory and preserves all arguments.
This is the inner verifier used after a nonzero product answer, not a product or ET oracle.

The interval scan follows the pinned `Scan.lean` procedure in the proof of Theorem 17
at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. The native code,
register layout and charged constants are rebuilt against the existing WordRAM APIs.
The stage definitions are internal implementation interfaces.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

namespace Reg

/-- Original canonical-signed A–B array pointer. -/
abbrev ab : Fin 32 := 9
/-- Original canonical-signed B–C array pointer. -/
abbrev bc : Fin 32 := 10
/-- Original canonical-signed A–C array pointer. -/
abbrev ac : Fin 32 := 11
/-- Outer matrix dimension. -/
abbrev size : Fin 32 := 12
/-- Original first query coordinate. -/
abbrev a : Fin 32 := 13
/-- Original second query coordinate. -/
abbrev b : Fin 32 := 14
/-- First original vertex of the scanned interval. -/
abbrev first : Fin 32 := 15
/-- Number of vertices in the interval. -/
abbrev length : Fin 32 := 16
/-- B–C row pointer at the first interval vertex. -/
abbrev rowB : Fin 32 := 17
/-- A–C row pointer at the first interval vertex. -/
abbrev rowA : Fin 32 := 18
/-- Cached canonical-signed A–B weight. -/
abbrev wab : Fin 32 := 19
/-- Number of interval vertices already tested. -/
abbrev index : Fin 32 := 20
/-- Unsigned success flag. -/
abbrev found : Fin 32 := 21
/-- Original vertex of the most recently verified zero sum. -/
abbrev witness : Fin 32 := 22
/-- Constant one. -/
abbrev one : Fin 32 := 23
/-- Actual load-address temporary. -/
abbrev address : Fin 32 := 24
/-- Constant zero, preserved by the signed arithmetic bank. -/
abbrev zero : Fin 32 := 25

end Reg

/-- Ordinary runtime arguments of the original-weight interval verifier. This stores no
execution, fit, witness or time certificate. -/
structure Args where
  /-- Original canonical-signed A–B array base. -/
  ab : ℕ
  /-- Original canonical-signed B–C array base. -/
  bc : ℕ
  /-- Original canonical-signed A–C array base. -/
  ac : ℕ
  /-- Matrix dimension. -/
  n : ℕ
  /-- First query coordinate. -/
  a : ℕ
  /-- Second query coordinate. -/
  b : ℕ
  /-- First interval vertex. -/
  first : ℕ
  /-- Number of interval vertices. -/
  length : ℕ

/-- The eight scalar arguments occupy their actual native registers. -/
@[expose] def Args.InRegisters (A : Args) (x : Data 32) : Prop :=
  x.regs Reg.ab = A.ab ∧ x.regs Reg.bc = A.bc ∧ x.regs Reg.ac = A.ac ∧
    x.regs Reg.size = A.n ∧ x.regs Reg.a = A.a ∧ x.regs Reg.b = A.b ∧
    x.regs Reg.first = A.first ∧ x.regs Reg.length = A.length

/-- A concrete numerical envelope for all address/index arithmetic in this verifier. -/
@[expose] def Args.addressBound (A : Args) : ℕ :=
  A.ab + A.bc + A.ac + 3 * (A.n * A.n) + A.n + A.first + A.length + 8

open Reg in
/-- Load the fixed A–B weight and compute the two row pointers with actual instructions. -/
@[expose] def setup : Code .standard 32 := ram[
  one ← #1; zero ← #0; found ← #0; index ← #0; witness ← first;
  address ← a * size; address ← address + b; address ← address + ab; wab ← *address;
  rowB ← b * size; rowB ← rowB + first; rowB ← rowB + bc;
  rowA ← a * size; rowA ← rowA + first; rowA ← rowA + ac ]

open Reg in
/-- First two original signed weights, read from the original memory. -/
@[expose] def loadBC : Code .standard 32 := ram[
  Signed.left ← wab; address ← rowB + index; Signed.right ← *address ]

open Reg in
/-- The true partial sum and the original A–C weight. -/
@[expose] def loadAC : Code .standard 32 := ram[
  Signed.left ← Signed.result; address ← rowA + index; Signed.right ← *address ]

/-- Two charged standard-native signed additions, with no extra machine operation. -/
@[expose] def testVertex : Code .standard 32 :=
  .seq loadBC (.seq Signed.add (.seq loadAC Signed.add))

open Reg in
/-- Remember a genuine zero-sum vertex, then advance the interval counter. -/
@[expose] def finishVertex : Code .standard 32 := ram[
  if Signed.result = zero then [ found ← one; witness ← first + index ]
  else [ witness ← witness ]; index ← index + one ]

/-- One complete verification step. -/
@[expose] def step : Code .standard 32 := .seq testVertex finishVertex

/-- Fixed native interval verifier; only the actual loop count depends on input. -/
@[expose] def program : Code .standard 32 :=
  .seq setup (.loop (.lt Reg.index Reg.length) step)

/-- Fixed instruction graph, independent of dimensions and physical width. -/
theorem program_fixed : program.size ≤ 160 ∧ ¬program.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
