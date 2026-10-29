/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeLayout

/-!
# Complete fixed native program for one Chan–He node

The source comparator is [NodeArray.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/NodeArray.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The layout, native code and proofs are original. The source's `Light` machine is not imported.

## Main definitions

* `NodePacking.program`: computes the layout and tags, pads every output cell, then performs
  three actual residue/histogram/extraction/placement calls, including all three count stores.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM

/-- The three supplied signed input bases. -/
def source (j : Fin 3) : Fin 64 := ⟨46 + 2 * j.val, by omega⟩
/-- The three supplied input lengths. -/
def length (j : Fin 3) : Fin 64 := ⟨47 + 2 * j.val, by omega⟩
/-- Fresh allocation base after all input arrays. -/
abbrev base : Fin 64 := 52
/-- Common number of four-cell groups. -/
abbrev groups : Fin 64 := 53
/-- Node input magnitude bound. -/
abbrev magnitude : Fin 64 := 54
/-- Positive modulus. -/
abbrev modulus : Fin 64 := 55
/-- Computed residue workspace base. -/
abbrev scratch : Fin 64 := 56
/-- Computed histogram workspace base. -/
abbrev histogram : Fin 64 := 57
/-- Computed packed output base. -/
abbrev packed : Fin 64 := 58
/-- Twice the gap `G=6U+4`, ready for sign-and-magnitude tagging. -/
abbrev gap : Fin 64 := 59
/-- Twice the padding magnitude `W=2U+1`. -/
abbrev padding : Fin 64 := 60
/-- Setup scratch. -/
abbrev temporary : Fin 64 := 61
/-- Constant one, retained across the complete calls. -/
abbrev one : Fin 64 := 62
/-- Constant four, retained across the complete calls. -/
abbrev four : Fin 64 := 63

/-- The mathematical layout determined by the runtime parameters. -/
def layout (x : Data 64) : Layout :=
  ⟨x.regs base, fun j => x.regs (length j), x.regs groups, x.regs modulus, x.regs magnitude⟩

/-- Padding workspace embedded below all persistent node parameters. -/
def paddingRegisters (i : Fin 10) : Fin 64 := ⟨i.val, by omega⟩

@[inherit_doc Padding.dst]
abbrev pdst : Fin 64 := paddingRegisters Padding.dst
@[inherit_doc Padding.len]
abbrev plen : Fin 64 := paddingRegisters Padding.len
@[inherit_doc Padding.pad0]
abbrev pad0 : Fin 64 := paddingRegisters Padding.pad0
@[inherit_doc Padding.pad1]
abbrev pad1 : Fin 64 := paddingRegisters Padding.pad1
@[inherit_doc Padding.pad2]
abbrev pad2 : Fin 64 := paddingRegisters Padding.pad2
@[inherit_doc Padding.pad3]
abbrev pad3 : Fin 64 := paddingRegisters Padding.pad3

/-- Compute every permanent and scratch block address in twelve native instructions. -/
def layoutCode : Code .standard 64 :=
  let n₀ := length 0
  let n₁ := length 1
  let n₂ := length 2
  ram[ one ← #1; four ← #4; temporary ← #3;
    packed ← base + temporary; packed ← packed + n₀; packed ← packed + n₁;
    packed ← packed + n₂; scratch ← four * groups; scratch ← packed + scratch;
    histogram ← scratch + n₀; histogram ← histogram + n₁; histogram ← histogram + n₂ ]

/-- Compute the exact positive encoded padding pattern, including all signed-negation/tag work.
The third padding word uses subtraction because its integer contribution is `-W`. -/
def constantsCode : Code .standard 64 := ram[
  padding ← magnitude + magnitude; padding ← padding + one; padding ← padding + padding;
  gap ← temporary * padding; temporary ← #2; gap ← gap + temporary;
  pad0 ← #10; pad0 ← pad0 * gap; pad1 ← padding + gap;
  temporary ← #3; pad2 ← temporary * gap; pad2 ← pad2 + padding;
  pad3 ← four * gap; pad3 ← pad3 - padding; pdst ← packed; plen ← groups ]

/-- Compute the selected heavy-array descriptor address. The choice is one of three fixed
pieces of code, never a program whose size depends on an input length. -/
def descriptorCode (j : Fin 3) : Code .standard 64 :=
  let d := CountPlace.descriptor
  let n₀ := length 0
  let n₁ := length 1
  if j = 0 then ram[ d ← base ] else if j = 1 then ram[ d ← base + one; d ← d + n₀ ]
  else ram[ d ← base + one; d ← d + n₀; d ← d + one; d ← d + n₁ ]

/-- Deliver the exact encoded tag for one fixed column. -/
def tagCode (j : Fin 3) : Code .standard 64 :=
  let t := CountPlace.tag
  if j = 0 then ram[ t ← gap ] else if j = 1 then ram[ temporary ← #3; t ← temporary * gap ]
  else ram[ t ← four * gap ]

/-- Deliver the duplicated-Z distance; the other columns perform two coincident stores. -/
def distanceCode (j : Fin 3) : Code .standard 64 :=
  let d := CountPlace.distance
  if j = 2 then ram[ d ← four * modulus ] else ram[ d ← #0 ]

/-- Every runtime input and output parameter is explicitly delivered to the complete call. -/
def prepare (j : Fin 3) : Code .standard 64 :=
  let n := length j
  let s := source j
  let l := CountPlace.len
  let a := CountPlace.src
  let k := CountPlace.scratch
  let h := CountPlace.hist
  let d := CountPlace.descriptor
  let o := CountPlace.heavy
  let p := CountPlace.packed
  let m := CountPlace.modulus
  let c := CountPlace.column
  let neg := CountPlace.negative
  .seq (ram[ l ← n; a ← s; k ← scratch; h ← histogram ])
    (.seq (descriptorCode j) (.seq (ram[ o ← d + one; p ← packed; m ← modulus ])
      (.seq (tagCode j) (.seq (.op (.const c (j.val + 1)))
        (.seq (distanceCode j) (.op (.const neg (if j = 2 then 1 else 0))))))))

/-- Complete one-set native round with charged setup and a written heavy count. -/
def round (j : Fin 3) : Code .standard 64 := .seq (prepare j) CountPlace.program

/-- Complete charged address/tag/padding initialization. -/
def initializeCode : Code .standard 64 :=
  .seq layoutCode (.seq constantsCode (Padding.program.rename paddingRegisters))

/-- Complete one-node preprocessing. This code is independent of `n,w,M,N,U`. -/
def program : Code .standard 64 :=
  .seq initializeCode (.seq (round 0) (.seq (round 1) (round 2)))

/-- The original three input bases/lengths and base, length, magnitude and modulus parameters
are preserved by the complete program. -/
theorem preserves_parameters (i : Fin 64) (hi : 46 ≤ i.val ∧ i.val ≤ 55) :
    program.Preserves i := by
  fin_cases i <;> norm_num at hi <;> decide

/-- The assembled code length has a fixed bound, independent of every runtime parameter. -/
theorem size_program_le : program.size ≤ 4096 := by decide

/-- The complete program is deterministic and never reads the word width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

/-- No instruction samples randomness or invokes an oracle. -/
theorem isRandFree : program.IsRandFree := by decide

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
