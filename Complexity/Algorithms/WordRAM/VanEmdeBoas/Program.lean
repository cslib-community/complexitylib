/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation

/-!
# Fixed native word-RAM van Emde Boas code

The same thirty-two-register structured program dispatches insertion, membership and strict
successor. It uses only standard unsigned integer operations, comparisons, loads and stores.
The split size and child span are read from the represented memory; no code is generated from
the depth, key or word width.

The minimum is stored outside recursive clusters, following
[Demaine's exposition][Demaine2015VanEmdeBoas]. The lecture notes credit Michael Bender.
The five-word contiguous records and explicit four-word successor return stack are engineering
choices, distinguished from the original stratified representation of
[van Emde Boas, Kaas and Zijlstra][VanEmdeBoasKaasZijlstra1977].

These definitions alone establish no operation's correctness, execution bound, initialization
or space use. Each certified operation must supply actual execution and representation proofs.
In particular, a fitting query word may exceed the tree universe; membership rejects queries
above the cached maximum before computing a descendant address.

## Main definitions

* `tag`, `arg`, `out`, `found`, `root`, `stackBase`, `depth`, `tableBase`, `zero`, `one`, `two`,
  `three`, `four`, `five`, `p`, `x`, `q`, `t`, `high`, `low`, `child`, `addr`, `present`, `mn`,
  `mx`, `tmp`, `sp`, `runFlag`, `kind`, `payload`, `frameQ`, `frameT`: the thirty-two named
  registers of the van Emde Boas machine program.
* `setup`, `coordinates`, `finishMin`, `finishMax`, `finishNone`, `pushFrame`, `descendCluster`,
  `descendSummary`, `popFrame`: register setup, coordinate splitting, termination, and return-stack
  frame subroutines.
* `program`: one fixed dispatch over native instructions.
* `memberBody`, `memberLoop`: membership descent with a cached-maximum rejection.
* `insertBody`, `insertLoop`: native insertion descent.
* `successorDescentBody`, `successorDescent`, `successorUnwindBody`, `successorUnwind`:
  native strict-successor descent and return-stack unwinding.

## Main results

* `program_size`: the fixed dispatch has 212 instructions before halt.
* `program_not_readsWidth`: no instruction reads the selected word width.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
* [P. van Emde Boas, R. Kaas and E. Zijlstra, *Design and implementation of an efficient
  priority queue*][VanEmdeBoasKaasZijlstra1977]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM

/-- Caller-supplied operation tag: insertion = 0, membership = 1, successor = 2. -/
abbrev tag : Fin 32 := 0
/-- Caller-supplied key or query word. -/
abbrev arg : Fin 32 := 1
/-- Returned key or Boolean membership word. -/
abbrev out : Fin 32 := 2
/-- Presence flag distinguishing a successor from absence. -/
abbrev found : Fin 32 := 3
/-- Persistent base address of the represented tree. -/
abbrev root : Fin 32 := 4
/-- Persistent base address of the reserved return stack. -/
abbrev stackBase : Fin 32 := 5
/-- Reserved register for initialization depth; the dispatch program does not read it. -/
abbrev depth : Fin 32 := 6
/-- Reserved register for initialization metadata; the dispatch program does not read it. -/
abbrev tableBase : Fin 32 := 7
/-- Register holding zero after setup. -/
abbrev zero : Fin 32 := 8
/-- Register holding one after setup. -/
abbrev one : Fin 32 := 9
/-- Register holding two after setup. -/
abbrev two : Fin 32 := 10
/-- Register holding three after setup. -/
abbrev three : Fin 32 := 11
/-- Register holding four after setup. -/
abbrev four : Fin 32 := 12
/-- Register holding the five-word header size after setup. -/
abbrev five : Fin 32 := 13
/-- Current subtree address. -/
abbrev p : Fin 32 := 14
/-- Current local query or inserted key. -/
abbrev x : Fin 32 := 15
/-- Current node's stored split size. -/
abbrev q : Fin 32 := 16
/-- Current node's stored child span. -/
abbrev t : Fin 32 := 17
/-- High part of the current key. -/
abbrev high : Fin 32 := 18
/-- Low part of the current key. -/
abbrev low : Fin 32 := 19
/-- Computed child address. -/
abbrev child : Fin 32 := 20
/-- Scratch address for indexed memory operations. -/
abbrev addr : Fin 32 := 21
/-- Cached presence flag read from the current record. -/
abbrev present : Fin 32 := 22
/-- Cached minimum read from a record. -/
abbrev mn : Fin 32 := 23
/-- Cached maximum read from a record. -/
abbrev mx : Fin 32 := 24
/-- Scratch arithmetic register. -/
abbrev tmp : Fin 32 := 25
/-- Return-stack cursor. -/
abbrev sp : Fin 32 := 26
/-- Whether the descent loop continues. -/
abbrev runFlag : Fin 32 := 27
/-- Return-frame tag: cluster = 0, summary = 1. -/
abbrev kind : Fin 32 := 28
/-- Return-frame payload: cluster offset or parent address. -/
abbrev payload : Fin 32 := 29
/-- Split size loaded from a return frame. -/
abbrev frameQ : Fin 32 := 30
/-- Child span loaded from a return frame. -/
abbrev frameT : Fin 32 := 31

/-- Initialize constants, traversal, result and stack registers in twelve instructions. -/
def setup : Code .standard 32 := ram[
  zero ← #0; one ← #1; two ← #2; three ← #3; four ← #4; five ← #5;
  p ← root; x ← arg; out ← zero; found ← zero; sp ← stackBase; runFlag ← one ]

/-- Split the key and compute its cluster address using six arithmetic instructions. -/
def coordinates : Code .standard 32 := ram[
  high ← x / q; low ← x % q; tmp ← high + one; tmp ← tmp * t;
  child ← p + five; child ← child + tmp ]

/-- Return the cached minimum and stop descent. -/
def finishMin : Code .standard 32 := ram[
  out ← mn; found ← one; runFlag ← zero ]

/-- Return the cached maximum and stop descent. -/
def finishMax : Code .standard 32 := ram[
  out ← mx; found ← one; runFlag ← zero ]

/-- Return absence and stop descent. -/
def finishNone : Code .standard 32 := ram[
  out ← zero; found ← zero; runFlag ← zero ]

/-- One native insertion iteration. Empty records and empty destination clusters install their
first key directly in the three-word bounds area. -/
def insertBody : Code .standard 32 := ram[
  present ← *p;
  if present = zero then [
    *p ← one; ⟪writeAt addr p one x⟫; ⟪writeAt addr p two x⟫; runFlag ← zero
  ] else [
    ⟪readAt addr mn p one⟫;
    if x = mn then [ runFlag ← zero ] else [
      if x < mn then [ ⟪writeAt addr p one x⟫; x ← mn ] else [ x ← x ];
      ⟪readAt addr mx p two⟫;
      if mx < x then [ ⟪writeAt addr p two x⟫ ] else [ mx ← mx ];
      ⟪readAt addr q p three⟫;
      if q = zero then [ runFlag ← zero ] else [
        ⟪readAt addr t p four⟫; ⟪coordinates⟫; present ← *child;
        if present = zero then [
          *child ← one; ⟪writeAt addr child one low⟫; ⟪writeAt addr child two low⟫;
          p ← p + five; x ← high
        ] else [ p ← child; x ← low ]
      ]
    ]
  ] ]

/-- Native insertion descent. -/
def insertLoop : Code .standard 32 := ram[
  while zero < runFlag do [ ⟪insertBody⟫ ] ]

/-- One native membership iteration. The maximum check rejects large queries before descent. -/
def memberBody : Code .standard 32 := ram[
  present ← *p;
  if present = zero then [ runFlag ← zero ] else [
    ⟪readAt addr mn p one⟫;
    if x = mn then [ out ← one; runFlag ← zero ] else [
      ⟪readAt addr mx p two⟫;
      if x = mx then [ out ← one; runFlag ← zero ] else [
        if x < mx then [
          ⟪readAt addr q p three⟫;
          if q = zero then [ runFlag ← zero ] else [
            ⟪readAt addr t p four⟫; ⟪coordinates⟫; p ← child; x ← low
          ]
        ] else [ runFlag ← zero ]
      ]
    ]
  ] ]

/-- Native membership descent, with one depth decrease for each continuing iteration. -/
def memberLoop : Code .standard 32 := ram[
  while zero < runFlag do [ ⟪memberBody⟫ ] ]

/-- Push four words: continuation kind, payload, split and child span. -/
def pushFrame : Code .standard 32 := ram[
  *sp ← kind; sp ← sp + one; *sp ← payload; sp ← sp + one;
  *sp ← q; sp ← sp + one; *sp ← t; sp ← sp + one ]

/-- Save a cluster-return continuation and descend into the selected cluster. -/
def descendCluster : Code .standard 32 := ram[
  kind ← zero; payload ← high * q; ⟪pushFrame⟫; p ← child; x ← low ]

/-- Save a summary-return continuation and descend into the summary. -/
def descendSummary : Code .standard 32 := ram[
  kind ← one; payload ← p; ⟪pushFrame⟫; p ← p + five; x ← high ]

/-- One native successor-descent iteration. The cached maximum chooses between early termination,
cluster descent and summary descent. -/
def successorDescentBody : Code .standard 32 := ram[
  present ← *p;
  if present = zero then [ ⟪finishNone⟫ ] else [
    ⟪readAt addr mn p one⟫;
    if x < mn then [ ⟪finishMin⟫ ] else [
      ⟪readAt addr mx p two⟫;
      if x < mx then [
        ⟪readAt addr q p three⟫;
        if q = zero then [ ⟪finishMax⟫ ] else [
          ⟪readAt addr t p four⟫; ⟪coordinates⟫; present ← *child;
          if present = zero then [ ⟪descendSummary⟫ ] else [
            ⟪readAt addr mx child two⟫;
            if low < mx then [ ⟪descendCluster⟫ ] else [ ⟪descendSummary⟫ ]
          ]
        ]
      ] else [ ⟪finishNone⟫ ]
    ]
  ] ]

/-- Native successor descent. -/
def successorDescent : Code .standard 32 := ram[
  while zero < runFlag do [ ⟪successorDescentBody⟫ ] ]

/-- Pop the four-word return frame. -/
def popFrame : Code .standard 32 := ram[
  sp ← sp - one; frameT ← *sp; sp ← sp - one; frameQ ← *sp;
  sp ← sp - one; payload ← *sp; sp ← sp - one; kind ← *sp ]

/-- One native successor-unwind iteration. -/
def successorUnwindBody : Code .standard 32 := ram[
  ⟪popFrame⟫;
  if kind = zero then [ out ← payload + out ] else [
    high ← out; tmp ← high + one; tmp ← tmp * frameT;
    child ← payload + five; child ← child + tmp;
    ⟪readAt addr low child one⟫; out ← high * frameQ; out ← out + low
  ] ]

/-- Reconstruct the answer through cluster and summary return frames. -/
def successorUnwind : Code .standard 32 := ram[
  while stackBase < sp do [ ⟪successorUnwindBody⟫ ] ]

/-- One fixed dispatch program, independent of the universe, query, state and word width. -/
def program : Code .standard 32 := ram[
  ⟪setup⟫;
  if tag = zero then [ ⟪insertLoop⟫ ] else [
    if tag = one then [ ⟪memberLoop⟫ ] else [
      ⟪successorDescent⟫; ⟪successorUnwind⟫
    ]
  ] ]
/-- The fixed dispatch has 212 instructions before the final compiled halt. -/
theorem program_size : program.size = 212 := by decide

/-- The dispatch never reads the selected word width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.VanEmdeBoas

