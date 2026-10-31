/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PrimeTrial
public import Complexity.Computability.WordRAM.RegisterFrame
public import Complexity.Computability.WordRAM.Width

/-!
# Native minimum-count prime selection controller

The controller enumerates candidates starting at two while their square is less than `D`.
It tests the other endpoint by `D ≤ 4p²`, invokes actual trial division, and calls a supplied
finite counting program only on primes in that window. It retains the first strict minimum.
No prime list, bitmap or primality oracle is supplied.

The counting code occupies registers below 128 and uses the concrete CountPrime ABI:
64 is `n`, 65 is `p`, 66/67/68 are the three original signed matrix pointers, 69 is the dirty
workspace pointer, and 70 is the returned unsigned count. Selector metadata is above that bank.
This module defines a component controller parameterized by finite code. Its instantiation
with the concrete modular counter, correctness and complete width/resource composition are
separate obligations under #2098; this is not a completed prime-selection endpoint.

The selection policy adapts `chKeep`/`chRound` in Anthropic's
[ChoosePrime source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/ChoosePrime.lean).
The source first constructs a prime list; this
native controller instead enumerates by integer square tests and charged trial division.
Native instruction costs must be proved directly, independently of Light's cost model.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

namespace Reg

/-- Low-bank candidate delivered to trial division. -/
abbrev trialArg : Fin 160 := 0
/-- Low-bank primality bit returned by trial division. -/
abbrev trialFlag : Fin 160 := 2
/-- Side-length argument delivered to the modular counter. -/
abbrev countSide : Fin 160 := 64
/-- Prime argument delivered to the modular counter. -/
abbrev countPrime : Fin 160 := 65
/-- AB argument delivered to the modular counter. -/
abbrev countAB : Fin 160 := 66
/-- BC argument delivered to the modular counter. -/
abbrev countBC : Fin 160 := 67
/-- AC argument delivered to the modular counter. -/
abbrev countAC : Fin 160 := 68
/-- Workspace argument delivered to the modular counter. -/
abbrev countScratch : Fin 160 := 69
/-- Raw unsigned result returned by the modular counter. -/
abbrev countResult : Fin 160 := 70
/-- Selected prime, with zero denoting that no eligible prime has yet been seen. -/
abbrev best : Fin 160 := 128
/-- Raw modular count for the currently selected prime. -/
abbrev bestCount : Fin 160 := 129
/-- Whether a prime has already been counted. -/
abbrev found : Fin 160 := 130
/-- Original matrix side length. -/
abbrev side : Fin 160 := 131
/-- Original prime-window parameter `D`. -/
abbrev window : Fin 160 := 132
/-- Original canonical-signed AB matrix pointer. -/
abbrev inputAB : Fin 160 := 133
/-- Original canonical-signed BC matrix pointer. -/
abbrev inputBC : Fin 160 := 134
/-- Original canonical-signed AC matrix pointer. -/
abbrev inputAC : Fin 160 := 135
/-- Caller-disjoint reusable dirty workspace. -/
abbrev scratch : Fin 160 := 136
/-- Current candidate, beginning at two. -/
abbrev cursor : Fin 160 := 137
/-- Square of the current candidate. -/
abbrev square : Fin 160 := 138
/-- Four times the current candidate's square. -/
abbrev fourSquare : Fin 160 := 139
/-- Preserved constant one. -/
abbrev one : Fin 160 := 140
/-- Preserved constant zero. -/
abbrev zero : Fin 160 := 141
/-- Preserved constant four. -/
abbrev four : Fin 160 := 142

end Reg

/-- Embed the complete modular-counter bank, leaving selector metadata outside its image. -/
@[expose] def counterRegisters (i : Fin 128) : Fin 160 := ⟨i.val, by omega⟩

/-- Reserve the low six registers for the existing trial-division kernel. -/
@[expose] def trialRegisters (i : Fin 6) : Fin 160 := ⟨i.val, by omega⟩

/-- CountPrime's actual argument delivery, followed by the supplied finite counting code. -/
@[expose] def count (counter : Code .standard 128) : Code .standard 160 :=
  .seq (ram[ Reg.countSide ← Reg.side; Reg.countPrime ← Reg.cursor;
    Reg.countAB ← Reg.inputAB; Reg.countBC ← Reg.inputBC;
    Reg.countAC ← Reg.inputAC; Reg.countScratch ← Reg.scratch ])
    (counter.rename counterRegisters)

/-- Retain the first strict minimum, preserving the earlier prime on ties. -/
@[expose] def keep : Code .standard 160 := ram[
  if Reg.found = Reg.zero then [
    Reg.best ← Reg.cursor; Reg.bestCount ← Reg.countResult; Reg.found ← Reg.one
  ] else [
    if Reg.countResult < Reg.bestCount then [
      Reg.best ← Reg.cursor; Reg.bestCount ← Reg.countResult
    ] else [ Reg.best ← Reg.best ]
  ] ]

/-- Retain the selected result in one charged instruction on an ineligible branch. -/
@[expose] def nop : Code .standard 160 := ram[ Reg.best ← Reg.best ]

/-- Deliver the candidate to the actual low-bank trial-division program. -/
@[expose] def trial : Code .standard 160 :=
  .seq (ram[ Reg.trialArg ← Reg.cursor ]) (PrimeTrial.program.rename trialRegisters)

/-- Enforce the lower endpoint, test primality, and count/update only eligible primes. -/
@[expose] def candidate (counter : Code .standard 128) : Code .standard 160 :=
  .branch (.lt Reg.fourSquare Reg.window) nop
    (.seq trial (.branch (.eq Reg.trialFlag Reg.one) (.seq (count counter) keep) nop))

/-- One actual candidate test/count and advance, including both square computations. -/
@[expose] def body (counter : Code .standard 128) : Code .standard 160 :=
  .seq (ram[ Reg.fourSquare ← Reg.four * Reg.square ])
    (.seq (candidate counter)
      (ram[ Reg.cursor ← Reg.cursor + Reg.one; Reg.square ← Reg.cursor * Reg.cursor ]))

/-- Enumerate exactly the integer square window and retain the first minimum modular count.
The finite counting program is a code argument, not a runtime result or counting oracle. -/
@[expose] def program (counter : Code .standard 128) : Code .standard 160 :=
  .seq (ram[ Reg.one ← #1; Reg.zero ← #0; Reg.four ← #4;
    Reg.cursor ← #2; Reg.square ← #4;
    Reg.best ← #0; Reg.bestCount ← #0; Reg.found ← #0 ])
    (.loop (.lt Reg.square Reg.window) (body counter))

/-- The selector adds fifty flat slots to the single embedded counter body. -/
theorem program_size (counter : Code .standard 128) :
    (program counter).size = counter.size + 50 := by
  simp only [program, body, candidate, trial, count, keep, nop, PrimeTrial.program,
    PrimeTrial.body, Code.size, Code.size_rename]
  omega

/-- A counter that does not inspect word width gives a selector that does not inspect it. -/
theorem not_readsWidth {counter : Code .standard 128} (hc : ¬counter.ReadsWidth) :
    ¬(program counter).ReadsWidth := by
  have ht : ¬trial.ReadsWidth := by decide
  have hk : ¬keep.ReadsWidth := by decide
  have hn : ¬nop.ReadsWidth := by decide
  simpa [program, body, candidate, count, Code.ReadsWidth, Code.readsWidth_rename,
    ht, hk, hn, Op.ReadsWidth, Op.bin] using hc

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
