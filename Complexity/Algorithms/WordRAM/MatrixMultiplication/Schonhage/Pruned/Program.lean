/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes
public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Fixed native code for pruned tensor queries

The controller uses an explicit depth-first stack. Query and value directories have one row
per depth. A shared timestamp directory deduplicates child suffixes without clearing a dense
array at every node. Encoded products and sums use the existing native signed kernels.

## Main definitions

* `PrunedQuery.kernel`: evaluator with explicit caller-supplied array and scratch addresses.
* `PrunedQuery.program`: initialized-input wrapper computing all addresses from the depth and
  query-count headers.

## References

The query-set recursion is from [AlmanWilliams2026, Section 2.4.2], selectively adapted from
Anthropic's formal-math revision `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
[pinned source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/Recursion.lean). The explicit iterative stack and
timestamp implementation are new native code; the source machine is not imported.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The program has a fixed register bank, including nine signed-arithmetic scratch registers. -/
abbrev registers : ℕ := 96

abbrev inputDepth : Fin registers := 9
abbrev span : Fin registers := 10
abbrev arrayA : Fin registers := 11
abbrev arrayB : Fin registers := 12
abbrev queries : Fin registers := 13
abbrev queryCount : Fin registers := 14
abbrev output : Fin registers := 15
abbrev scratch : Fin registers := 16
abbrev epoch : Fin registers := 17
abbrev frames : Fin registers := 18
abbrev lists : Fin registers := 19
abbrev values : Fin registers := 20
abbrev stamps : Fin registers := 21
abbrev level : Fin registers := 22
abbrev mode : Fin registers := 23
abbrev active : Fin registers := 24
abbrev one : Fin registers := 25
abbrev ten : Fin registers := 26
abbrev nine : Fin registers := 27
abbrev frameWidth : Fin registers := 28
abbrev frame : Fin registers := 29
abbrev count : Fin registers := 30
abbrev leafPrefix : Fin registers := 31
abbrev stride : Fin registers := 32
abbrev term : Fin registers := 33
abbrev index : Fin registers := 34
abbrev childCount : Fin registers := 35
abbrev query : Fin registers := 36
abbrev digit : Fin registers := 37
abbrev suffix : Fin registers := 38
abbrev address : Fin registers := 39
abbrev temporary : Fin registers := 40
abbrev temporary₂ : Fin registers := 41
abbrev temporary₃ : Fin registers := 42
abbrev marker : Fin registers := 43
abbrev listBase : Fin registers := 44
abbrev valueBase : Fin registers := 45
abbrev childList : Fin registers := 46
abbrev childValues : Fin registers := 47
abbrev nextLevel : Fin registers := 48
abbrev childFrame : Fin registers := 49
abbrev childPrefix : Fin registers := 50
abbrev childStride : Fin registers := 51
abbrev nil : Fin registers := 52
abbrev two : Fin registers := 53

/-- Constant initialization, before the depth-controlled power loop. -/
def powerSetup : Code .standard registers := ram[
  nil ← #0; one ← #1; two ← #2; ten ← #10; nine ← #9; frameWidth ← #4;
  span ← #1; index ← #0 ]

/-- One charged power multiplication and counter increment. -/
def powerStep : Code .standard registers := ram[
  span ← span * ten; index ← index + one ]

/-- Initialize constants and compute the actual encoding-array length `10^L`. -/
def powers : Code .standard registers := ram[
  ⟪powerSetup⟫; while index < inputDepth do [ ⟪powerStep⟫ ] ]

/-- Separate stack frames, query lists, value directories and membership timestamps. -/
def locate : Code .standard registers := ram[
  frames ← scratch;
  temporary ← inputDepth + one; temporary₂ ← temporary * frameWidth;
  lists ← frames + temporary₂;
  temporary₂ ← temporary * span; values ← lists + temporary₂;
  stamps ← values + temporary₂ ]

/-- Append one previously unseen suffix and mark it with the current epoch. -/
def emit : Code .standard registers := ram[
  address ← stamps + suffix; marker ← *address;
  if marker = epoch then [ temporary ← temporary ] else [
    address ← childList + childCount; *address ← suffix;
    address ← stamps + suffix; *address ← epoch;
    childCount ← childCount + one ] ]

/-- The two fixed suffix kernels either divide a selected child query or copy a root query. -/
def putSuffix (child : Bool) : Code .standard registers :=
  .seq (if child then ram[ suffix ← query / ten ] else ram[ suffix ← query ]) emit

/-- A selected child suffix is computed by an actual unsigned division. -/
def selectSuffix : Code .standard registers := putSuffix true

/-- Load the next supplied query and compute its actual first digit. -/
def scanLoad : Code .standard registers := ram[
  address ← listBase + index; query ← *address; digit ← query % ten ]

/-- Root queries are copied directly; child queries are filtered by the native digit tests. -/
def scanDispatch (child : Bool) : Code .standard registers :=
  if child then ram[
      if digit = nine then [ ⟪selectSuffix⟫ ] else [
        if digit = term then [ ⟪selectSuffix⟫ ] else [ temporary ← temporary ] ] ]
  else putSuffix false

/-- One deduplicating scan step, including input indexing, dispatch and counter increment. -/
def scanStep (child : Bool) : Code .standard registers := ram[
  ⟪scanLoad⟫; ⟪scanDispatch child⟫; index ← index + one ]

/-- Initialize one query scan with a genuinely fresh native epoch. -/
def scanSetup : Code .standard registers := ram[
  epoch ← epoch + one; childCount ← #0; index ← #0 ]

/-- Scan and deduplicate an explicit source list. -/
def scan (child : Bool) : Code .standard registers := ram[
  ⟪scanSetup⟫; while index < count do [ ⟪scanStep child⟫ ] ]

/-- Deduplicate supplied queries into the root list; the original list remains read-only. -/
def rootList : Code .standard registers := ram[
  listBase ← queries; count ← queryCount; childList ← lists; ⟪scan false⟫;
  address ← frames; *address ← childCount;
  address ← address + one; *address ← nil;
  address ← address + one; *address ← one;
  address ← address + one; *address ← nil;
  level ← #0; mode ← #0; active ← #1 ]

/-- Load the current frame and compute its depth-specific list/value addresses. -/
def loadFrame : Code .standard registers := ram[
  frame ← level * frameWidth; frame ← frames + frame;
  address ← frame; count ← *address;
  address ← address + one; leafPrefix ← *address;
  address ← address + one; stride ← *address;
  address ← address + one; term ← *address;
  temporary ← level * span; listBase ← lists + temporary;
  valueBase ← values + temporary;
  nextLevel ← level + one; temporary ← nextLevel * span;
  childList ← lists + temporary; childValues ← values + temporary ]

/-- Return to the parent's accumulation phase, or finish the root. -/
def pop : Code .standard registers := ram[
  if level = nil then [ active ← #0 ] else [ level ← level - one; mode ← #2 ] ]

/-- Load both actual encoded words at the current leaf prefix. -/
def leafLoad : Code .standard registers := ram[
  address ← arrayA + leafPrefix; left ← *address;
  address ← arrayB + leafPrefix; right ← *address ]

/-- One requested leaf product, using the existing native signed multiplication kernel. -/
def leafProduct : Code .standard registers := ram[
  ⟪leafLoad⟫; ⟪multiply⟫; *valueBase ← result ]

/-- Evaluate a requested leaf from the actual two encoded words. -/
def leaf : Code .standard registers := ram[
  if nil < count then [ ⟪leafProduct⟫ ] else [ temporary ← temporary ];
  ⟪pop⟫ ]

/-- One actual indexed store for an explicitly listed requested value. -/
def clearValueStep : Code .standard registers := ram[
  address ← listBase + index; query ← *address;
  address ← valueBase + query; *address ← nil; index ← index + one ]

/-- Clear exactly the requested parent values, not the full dense directory. -/
def clearRequested : Code .standard registers := ram[
  index ← #0; while index < count do [ ⟪clearValueStep⟫ ] ]

/-- Store the actual next-term counter and enter the frame's dispatch phase. -/
def storeTerm : Code .standard registers := ram[
  address ← frame + frameWidth; address ← address - one;
  *address ← term; mode ← #1 ]

/-- Initialize the stored next-term counter after sparse accumulator clearing. -/
def clearValuesFinish : Code .standard registers := ram[ term ← #0; ⟪storeTerm⟫ ]

/-- Initialize requested values and the frame's next-term counter. -/
def clearValues : Code .standard registers := ram[
  ⟪clearRequested⟫; ⟪clearValuesFinish⟫ ]

/-- Entry phase: multiply at a leaf; otherwise initialize the requested accumulators. -/
def enter : Code .standard registers := ram[
  if level = inputDepth then [ ⟪leaf⟫ ] else [ ⟪clearValues⟫ ] ]

/-- Form and deduplicate a child request set using actual tests, loads and stores. -/
def buildChild : Code .standard registers := scan true

/-- Advance the parent's term after an empty child or after accumulating its returned values. -/
def advance : Code .standard registers := ram[
  term ← term + one; ⟪storeTerm⟫ ]

/-- Push a nonempty child, with the exact least-significant-first leaf leafPrefix. -/
def push : Code .standard registers := ram[
  childFrame ← nextLevel * frameWidth; childFrame ← frames + childFrame;
  temporary₂ ← term * stride; childPrefix ← leafPrefix + temporary₂;
  childStride ← stride * ten;
  address ← childFrame; *address ← childCount;
  address ← address + one; *address ← childPrefix;
  address ← address + one; *address ← childStride;
  address ← address + one; *address ← nil;
  level ← nextLevel; mode ← #0 ]

/-- Dispatch the next of the ten actual terms, recursing only on nonempty computed sets. -/
def dispatch : Code .standard registers := ram[
  if term < ten then [
    ⟪buildChild⟫;
    if nil < childCount then [ ⟪push⟫ ] else [ ⟪advance⟫ ] ] else [ ⟪pop⟫ ] ]

/-- Load the two encoded operands at the actual parent query and child suffix addresses. -/
def addValueLoad : Code .standard registers := ram[
  suffix ← query / ten;
  address ← valueBase + query; left ← *address;
  address ← childValues + suffix; right ← *address ]

/-- Store the signed sum back at the computed parent query address. -/
def addValueStore : Code .standard registers := ram[
  address ← valueBase + query; *address ← result ]

/-- Add one returned child value to its parent's actual signed accumulator. -/
def addValue : Code .standard registers := ram[
  ⟪addValueLoad⟫; ⟪add⟫; ⟪addValueStore⟫ ]

/-- Select the returned child by the same two real digit comparisons as child construction. -/
def accumulateDispatch : Code .standard registers := ram[
  if digit = nine then [ ⟪addValue⟫ ] else [
    if digit = term then [ ⟪addValue⟫ ] else [ temporary ← temporary ] ] ]

/-- Load, dispatch and advance one actual parent query. -/
def accumulateStep : Code .standard registers := ram[
  ⟪scanLoad⟫; ⟪accumulateDispatch⟫; index ← index + one ]

/-- Consume a returned child's values at the explicitly listed contributing parent queries. -/
def accumulateLoop : Code .standard registers := ram[
  index ← #0; while index < count do [ ⟪accumulateStep⟫ ] ]

/-- Traverse the parent requests once, then advance the stored term counter. -/
def accumulate : Code .standard registers := ram[ ⟪accumulateLoop⟫; ⟪advance⟫ ]

/-- One explicit-stack controller step. Every branch and frame address is native work. -/
def step : Code .standard registers := ram[
  ⟪loadFrame⟫;
  if mode = nil then [ ⟪enter⟫ ] else [
    if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]

/-- Report results in the original input query order, including repeated queries. -/
def report : Code .standard registers := ram[
  index ← #0;
  while index < queryCount do [
    address ← queries + index; query ← *address;
    address ← values + query; temporary ← *address;
    address ← output + index; *address ← temporary; index ← index + one ] ]

/-- The common stack evaluator after powers and caller parameters have been initialized. -/
def work : Code .standard registers := ram[
  ⟪locate⟫; ⟪rootList⟫;
  while nil < active do [ ⟪step⟫ ]; ⟪report⟫ ]

/-- Generic native evaluator with explicit pointer arguments and a fresh timestamp epoch. -/
def kernel : Code .standard registers := ram[ ⟪powers⟫; ⟪work⟫ ]

/-- Load the two ordinary scalar input headers. -/
def header : Code .standard registers := ram[
  address ← #1; inputDepth ← *address;
  address ← #2; queryCount ← *address ]

/-- Compute all initial array/output/scratch pointers from the actual array and query lengths. -/
def parameters : Code .standard registers := ram[
  arrayA ← #3; arrayB ← arrayA + span; queries ← arrayB + span;
  output ← queries + queryCount; scratch ← output + queryCount; epoch ← #0 ]

/-- One finite program reading the header and encoded arrays from ordinary initialized memory. -/
def program : Code .standard registers := ram[
  ⟪header⟫; ⟪powers⟫; ⟪parameters⟫; ⟪work⟫ ]

/-- The same program is used at every word width; it never reads the physical word size. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

set_option maxRecDepth 4096 in
-- Flattening the fixed nested controller also expands its two signed arithmetic kernels.
/-- A fixed bound on both control code and all arithmetic blocks, including the final halt. -/
theorem program_length_le : (program.program output).length ≤ 4096 := by decide

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
