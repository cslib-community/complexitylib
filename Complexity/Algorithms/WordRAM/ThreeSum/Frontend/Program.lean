/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Scan
public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Layout
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters
public import Complexity.Algorithms.WordRAM.RadixSort.Deduplicate

/-!
# Initialized-input native distinct-position frontend

The ABI has 128 registers. Radix uses 0–15; frontend locals use 16–63; the existing parameter
program uses 64–87. Registers 88–90 return descriptor base, descriptor count and heap end.
Each descriptor has six words `(length, pointer)` for its three compact injective arrays.
Each array has capacity `n+1`, including the singleton zeros required when `n=0`.

## Main definitions

* `Arrays.program`: native enumeration and descriptor construction.
* `program`: parameters, explicit-bit radix deduplication, and all frontend arrays.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

namespace Arrays

open Select Scan

/-- Original input length and label-bit budget. -/
abbrev inputLen : Fin 48 := 27
@[inherit_doc inputLen] abbrev digits : Fin 48 := 28
/-- Number of split triples, total triple count and total array count. -/
abbrev splits : Fin 48 := 29
@[inherit_doc splits] abbrev triples : Fin 48 := 30
@[inherit_doc splits] abbrev arrays : Fin 48 := 31
/-- Capacity per compact array. -/
abbrev capacity : Fin 48 := 32
/-- Next payload address. -/
abbrev heap : Fin 48 := 33
/-- Descriptor table base. -/
abbrev descriptors : Fin 48 := 34
/-- Current array index, current triple and slot. -/
abbrev current : Fin 48 := 35
@[inherit_doc current] abbrev triple : Fin 48 := 36
@[inherit_doc current] abbrev slot : Fin 48 := 37
/-- Arithmetic temporary and final heap endpoint. -/
abbrev temp : Fin 48 := 38
@[inherit_doc temp] abbrev heapEnd : Fin 48 := 39

/-- Write the singleton-zero array, including on empty input. -/
def singleton : Code .standard 48 := ram[ *dst ← zero; out ← one ]

/-- Compute the exact array selection mode for the two multiplicity triples. -/
def extra : Code .standard 48 := ram[
  if triple = splits then [
    if slot = zero then [ mode ← three; ⟪Scan.program⟫ ] else [
      if slot = one then [ ⟪singleton⟫ ] else [ mode ← five; ⟪Scan.program⟫ ] ]
  ] else [
    if slot = zero then [ mode ← four; ⟪Scan.program⟫ ] else [ ⟪singleton⟫ ] ] ]

/-- Decode `β`, then `β'`, then `[false,true]`, and scan the indicated one of three arrays. -/
def splitSetup : Code .standard 48 := ram[
  beta ← triple / two; beta' ← beta % digits; beta ← beta / digits;
  digit ← triple % two; mode ← slot ]

/-- Split setup followed by the complete compacting scan. -/
def split : Code .standard 48 := .seq splitSetup Scan.program

/-- Native choice between the split prefix and the two multiplicity triples. -/
def pick : Code .standard 48 := .branch (.lt triple splits) split extra

/-- Write a compact array's two descriptor words and advance the allocation cursor. -/
def writeDescriptor : Code .standard 48 := ram[
  addr ← current + current; addr ← addr + descriptors; *addr ← out;
  addr ← addr + one; *addr ← dst;
  heap ← heap + capacity; current ← current + one ]

/-- One complete array and its two descriptor words. -/
def body : Code .standard 48 :=
  .seq (ram[ triple ← current / three; slot ← current % three; dst ← heap ])
    (.seq pick writeDescriptor)

/-- Initialize every constant, layout and cursor, then enumerate every array, including empties. -/
def setup : Code .standard 48 := ram[
  zero ← #0; one ← #1; two ← #2; three ← #3; four ← #4; five ← #5;
  beta ← #0; beta' ← #0; digit ← #0;
  capacity ← inputLen + one;
  splits ← digits * digits; splits ← splits * two;
  triples ← splits + two; arrays ← triples * three;
  temp ← arrays * two; heap ← descriptors + temp;
  temp ← arrays * capacity; heapEnd ← heap + temp;
  current ← #0 ]

/-- Setup and all array iterations. -/
def program : Code .standard 48 := .seq setup (.loop (.lt current arrays) body)

end Arrays

/-- Embed the 24-register parameter program above both native kernels. -/
def parameterRegisters (i : Fin 24) : Fin 128 := ⟨64 + i.val, by omega⟩
/-- Embed the 16-register radix program in the low registers. -/
def radixRegisters (i : Fin 16) : Fin 128 := ⟨i.val, by omega⟩
/-- Embed the 48-register frontend program between radix and parameters. -/
def arrayRegisters (i : Fin 48) : Fin 128 := ⟨16 + i.val, by omega⟩

/-- Final descriptor base, descriptor count and one-past-end payload address. -/
abbrev descriptorBase : Fin 128 := 88
@[inherit_doc descriptorBase] abbrev descriptorCount : Fin 128 := 89
@[inherit_doc descriptorBase] abbrev heapEnd : Fin 128 := 90

/-- Setup for the lower-level sorter with the magnitude-derived bit bound, never physical width. -/
def radixSetup : Code .standard 128 :=
  let n := parameterRegisters ChanHe.Parameters.len
  let B := parameterRegisters ChanHe.Parameters.digits
  let radixLen := radixRegisters RadixSort.len
  let radixSrc := radixRegisters RadixSort.src
  let radixDst := radixRegisters RadixSort.dst
  let radixBits := radixRegisters RadixSort.bits
  ram[
  radixLen ← n; radixSrc ← #1; radixDst ← radixLen + radixSrc; radixBits ← B ]

/-- Transfer actual parameters and radix outputs into the concrete frontend ABI. -/
def arraySetup : Code .standard 128 :=
  let n := parameterRegisters ChanHe.Parameters.len
  let U := parameterRegisters ChanHe.Parameters.magnitude
  let B := parameterRegisters ChanHe.Parameters.digits
  let distinct := radixRegisters Deduplicate.out
  let len := arrayRegisters Scan.len
  let mag := arrayRegisters Select.magnitude
  let inputLen := arrayRegisters Arrays.inputLen
  let digits := arrayRegisters Arrays.digits
  let keys := arrayRegisters Scan.keys
  let counts := arrayRegisters Scan.counts
  let descriptors := arrayRegisters Arrays.descriptors
  let one := arrayRegisters Select.one
  ram[
    len ← distinct; mag ← U; inputLen ← n; digits ← B; one ← #1;
    keys ← n + n; keys ← keys + one;
    counts ← keys + n; descriptors ← counts + n ]

/-- Return metadata while preserving parameter outputs and full radix key/count arrays. -/
def finish : Code .standard 128 :=
  let base := arrayRegisters Arrays.descriptors
  let count := arrayRegisters Arrays.triples
  let endpoint := arrayRegisters Arrays.heapEnd
  ram[ descriptorBase ← base; descriptorCount ← count; heapEnd ← endpoint ]

/-- Native frontend after the existing complete parameter program. -/
def construct : Code .standard 128 :=
  .seq radixSetup (.seq (RadixSort.deduplicateCode.rename radixRegisters)
    (.seq arraySetup (.seq (Arrays.program.rename arrayRegisters) finish)))

/-- One finite native program for each fixed polynomial magnitude exponent. -/
def program (κ : ℕ) : Code .standard 128 :=
  .seq ((ChanHe.Parameters.program κ).rename parameterRegisters) construct

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
