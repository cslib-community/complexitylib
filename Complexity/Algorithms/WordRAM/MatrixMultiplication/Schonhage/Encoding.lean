/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Full
public import Complexity.Computability.WordRAM.Signed.Arithmetic
public import Complexity.Computability.WordRAM.Copy

/-!
# Native shared tensor encoding

The two fixed programs use unsigned addresses and counters, and sign-and-magnitude encoded
integer entries. Address 1 holds the depth; the `7^L` encoded entries begin at address 2.
The ordinary `State.init` length header is at address 0. Output and scratch are consecutive
blocks of `10^L` cells immediately after the input. Each coordinate transform reads the
previous stage and writes the other buffer. No initialization of unread scratch is needed.
A final charged copy puts the result in the first buffer, also at depth zero.

The coordinate transform is a new iterative implementation of the linear forms in
[AlmanWilliams2026, Section 2.4.1]. The coefficients and mathematical encoding are selectively
adapted from Anthropic's formal-math revision `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
[`Step`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Step.lean)
and [`Recursion`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean). The source's
recursive machine and execution semantics are not used.

## Main definitions

* `Encoding.program`: fixed native code for either coefficient table.
* `Encoding.input`: concrete input for `State.init`, including the depth header.
* `Encoding.outputBase`, `Encoding.scratchBase`: disjoint output and scratch blocks.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Seven variable digits: the three outer variables, then the four inner variables. -/
def leftAt (s : Fin 7) : LeftVar :=
  if h : s.val < 3 then .x ⟨s.val, h⟩
  else .p ⟨(s.val - 3) / 2, by omega⟩ ⟨(s.val - 3) % 2, Nat.mod_lt _ (by decide)⟩

/-- Right-variable digits use the same order as the left-variable digits. -/
def rightAt (s : Fin 7) : RightVar :=
  if h : s.val < 3 then .y ⟨s.val, h⟩
  else .q ⟨(s.val - 3) / 2, by omega⟩ ⟨(s.val - 3) % 2, Nat.mod_lt _ (by decide)⟩

/-- Row-major order on the nine `P` terms, followed by `P0`. -/
def termAt (t : Fin 10) : Term :=
  if h : t.val < 9 then .P ⟨t.val / 3, by omega⟩ ⟨t.val % 3, Nat.mod_lt _ (by decide)⟩
  else .P0

/-- Explicit numbering of the seven left variables. -/
def leftDigits : Fin 7 ≃ LeftVar where
  toFun := leftAt
  invFun
    | .x i => ⟨i.val, by omega⟩
    | .p i j => ⟨3 + 2 * i.val + j.val, by omega⟩
  left_inv := by decide
  right_inv := by decide

/-- Explicit numbering of the seven right variables. -/
def rightDigits : Fin 7 ≃ RightVar where
  toFun := rightAt
  invFun
    | .y j => ⟨j.val, by omega⟩
    | .q i j => ⟨3 + 2 * i.val + j.val, by omega⟩
  left_inv := by decide
  right_inv := by decide

/-- Explicit numbering of all ten terms. -/
def termDigits : Fin 10 ≃ Term where
  toFun := termAt
  invFun
    | .P i j => ⟨3 * i.val + j.val, by omega⟩
    | .P0 => 9
  left_inv := by decide
  right_inv := by decide

/-- The left and right coefficient tables, with digits made explicit. -/
def coefficients (rightSide : Bool) (t : Fin 10) (s : Fin 7) : ℤ :=
  if rightSide then psi (termAt t) (rightAt s) else phi (termAt t) (leftAt s)

/-- Every actual coefficient is zero, one or minus one. -/
theorem coefficients_values (side : Bool) (t : Fin 10) (s : Fin 7) :
    coefficients side t s = 0 ∨ coefficients side t s = 1 ∨ coefficients side t s = -1 := by
  decide +revert

/-- The input block ends where the output block begins. -/
def outputBase (L : ℕ) : ℕ := 2 + 7 ^ L

/-- The scratch block immediately follows the entire output block. -/
def scratchBase (L : ℕ) : ℕ := outputBase L + 10 ^ L

/-- Concrete input: depth header followed by the signed input entries in flat order.
The caller encodes each integer with `Signed.encode` before passing the list to `State.init`.
The native unsigned length header is installed by `State.init` itself. -/
def input (L : ℕ) (a : Fin (7 ^ L) → ℤ) : List ℕ :=
  L :: List.ofFn (fun i => encode (a i))

/-- The concrete left-array input, using Mathlib's base-seven string numbering. -/
def inputL {L : ℕ} (a : LeftStr L → ℤ) : List ℕ :=
  input L fun i => a fun ℓ => leftAt (finFunctionFinEquiv.symm i ℓ)

/-- The concrete right-array input, in exactly the same flat memory layout. -/
def inputR {L : ℕ} (a : RightStr L → ℤ) : List ℕ :=
  input L fun i => a fun ℓ => rightAt (finFunctionFinEquiv.symm i ℓ)

/-- All thirty-two registers are fixed independently of depth and width. Registers 0–8
are precisely the existing signed-arithmetic workspace. -/
abbrev depth : Fin 32 := 9
@[inherit_doc depth] abbrev inputSize : Fin 32 := 10
@[inherit_doc depth] abbrev capacity : Fin 32 := 11
@[inherit_doc depth] abbrev src : Fin 32 := 12
@[inherit_doc depth] abbrev dst : Fin 32 := 13
@[inherit_doc depth] abbrev output : Fin 32 := 14
@[inherit_doc depth] abbrev scratch : Fin 32 := 15
@[inherit_doc depth] abbrev stride : Fin 32 := 16
@[inherit_doc depth] abbrev prefixes : Fin 32 := 17
@[inherit_doc depth] abbrev stage : Fin 32 := 18
@[inherit_doc depth] abbrev cell : Fin 32 := 19
@[inherit_doc depth] abbrev block : Fin 32 := 20
@[inherit_doc depth] abbrev term : Fin 32 := 21
@[inherit_doc depth] abbrev suffix : Fin 32 := 22
@[inherit_doc depth] abbrev address : Fin 32 := 23
@[inherit_doc depth] abbrev accumulator : Fin 32 := 24
@[inherit_doc depth] abbrev one : Fin 32 := 25
@[inherit_doc depth] abbrev seven : Fin 32 := 26
@[inherit_doc depth] abbrev ten : Fin 32 := 27
@[inherit_doc depth] abbrev group : Fin 32 := 28
@[inherit_doc depth] abbrev temporary : Fin 32 := 29
@[inherit_doc depth] abbrev stageSize : Fin 32 := 30

/-- One coefficient in `{0, 1, -1}` times one array entry. Zero coefficients cause no load.
Nonzero coefficients use the proved native signed addition or subtraction block. -/
def summand (s : Fin 7) (c : ℤ) : Code .standard 32 :=
  if c = 0 then ram[ accumulator ← accumulator ]
  else .seq (ram[
    temporary ← #s.val;
    address ← temporary * stride; address ← group + address;
    right ← *address; left ← accumulator ])
    (.seq (if c = 1 then add else subtract) (ram[ accumulator ← result ]))

/-- A finite unrolling of the seven coefficients. This recursion constructs code; it does
not recurse on the input depth. -/
def sumCode : List (Fin 7 × ℤ) → Code .standard 32
  | [] => ram[ accumulator ← accumulator ]
  | (s, c) :: rest => .seq (summand s c) (sumCode rest)

/-- One linear form, including accumulator initialization. -/
def form (side : Bool) (t : Fin 10) : Code .standard 32 :=
  .seq (ram[ accumulator ← #0 ])
    (sumCode (List.ofFn fun s => (s, coefficients side t s)))

/-- A fixed finite dispatch on the ten possible term digits. -/
def dispatch (side : Bool) : List (Fin 10) → Code .standard 32
  | [] => ram[ accumulator ← #0 ]
  | t :: rest => ram[
      temporary ← #t.val;
      if term = temporary then [ ⟪form side t⟫ ] else [ ⟪dispatch side rest⟫ ] ]

/-- Decode one flat output index into its mixed-radix coordinates and source group. -/
def cellSetup : Code .standard 32 := ram[
  temporary ← ten * stride;
  block ← cell / temporary;
  term ← cell / stride; term ← term % ten;
  suffix ← cell % stride;
  group ← block * seven; group ← group * stride;
  group ← group + suffix; group ← src + group ]

/-- Store the computed entry and advance the flat index. -/
def cellFinish : Code .standard 32 := ram[
  address ← dst + cell; *address ← accumulator;
  cell ← cell + one ]

/-- One output cell. The flat index is `(prefix * 10 + term) * stride + suffix`;
its seven source addresses are `(prefix * 7 + s) * stride + suffix`. -/
def cellBody (side : Bool) : Code .standard 32 :=
  .seq cellSetup (.seq (dispatch side (List.finRange 10)) cellFinish)

/-- Divide the suffix stride and compute the next stage size. -/
def stageHead : Code .standard 32 := ram[
  stride ← stride / seven;
  stageSize ← prefixes * ten; stageSize ← stageSize * stride;
  cell ← #0 ]

/-- Alternate the two buffers and advance the prefix and stage counters. -/
def stageTail : Code .standard 32 := ram[
  src ← dst;
  if dst = output then [ dst ← scratch ] else [ dst ← output ];
  prefixes ← prefixes * ten; stage ← stage + one ]

/-- Transform the next coordinate, then alternate the output buffers. -/
def stageBody (side : Bool) : Code .standard 32 :=
  .seq stageHead (.seq (.loop (.lt cell stageSize) (cellBody side)) stageTail)

/-- Load the actual depth header and initialize the power counters. -/
def setupHead : Code .standard 32 := ram[
  one ← #1; seven ← #7; ten ← #10;
  address ← #1; depth ← *address;
  inputSize ← #1; capacity ← #1; stage ← #0 ]

/-- One multiplication by each radix and one counter increment. -/
def powerBody : Code .standard 32 := ram[
  inputSize ← inputSize * seven; capacity ← capacity * ten; stage ← stage + one ]

/-- Compute the concrete buffer addresses from the powers and initialize the first stage. -/
def setupTail : Code .standard 32 := ram[
  temporary ← #2; output ← temporary + inputSize; scratch ← output + capacity;
  src ← #2; dst ← output; stride ← inputSize; prefixes ← #1; stage ← #0 ]

/-- Read the depth and compute both powers in a charged native loop. -/
def setup : Code .standard 32 :=
  .seq setupHead (.seq (.loop (.lt stage depth) powerBody) setupTail)

/-- Reuse the existing seven-register array copy inside the encoder's register file. -/
def copyRegisters : Fin 7 → Fin 32 := ![src, output, capacity, cell, address, accumulator, one]

/-- The seven copy registers are distinct. -/
theorem copyRegisters_injective : Function.Injective copyRegisters := by decide

/-- A charged copy into the fixed output block, permitting disjoint blocks in either order
or identical source and destination. -/
def copyOut : Code .standard 32 := ArrayCopy.program.rename copyRegisters

/-- The complete fixed native encoder, excluding its final halt. The returned `output`
register identifies the first output cell; the `capacity` register holds its length. -/
def program (side : Bool) : Code .standard 32 := ram[
  ⟪setup⟫;
  while stage < depth do [ ⟪stageBody side⟫ ];
  ⟪copyOut⟫ ]

/-- The code performs no word-width queries. -/
theorem program_readsWidth (side : Bool) : ¬(program side).ReadsWidth := by
  cases side <;> decide

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
