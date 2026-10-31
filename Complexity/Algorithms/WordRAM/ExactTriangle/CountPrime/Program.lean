/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
public import Complexity.Algorithms.WordRAM.NatClog

/-!
# Concrete native modular triangle-counting code

The program computes three actual unsigned residue arrays, a spread table by its binary
recurrence, two zero-padded cyclic-monomial matrices, the actual seven-product Strassen
product, and the selected coefficient sum. It contains no triple-enumeration loop and takes
no table, layout, multiplication, result or execution certificate as input.

Pointers, dimensions and modulus are unsigned words; the original three weight arrays hold
canonical signed words. Monomial coefficients are written directly as canonical signed
zero or one. The existing residue loop explicitly decodes its nonnegative remainders. The
last scan explicitly decodes the nonnegative product coefficients before unsigned addition.

The source algorithm is Programs/Sec3/Theorem17/Hashing/CountPrime.lean at pinned revision
16a5ce41304fcdaea4e0be7c132e1c361dc26da5. This native adaptation uses the genuine standard
division/remainder instructions and the existing signed remainder kernel instead of Light's
bit-doubling residue table. This module defines code only; the complete general native
correctness, logarithmic-width and charged subcubic resource claims need separate proofs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

namespace Reg

/-- Low helper-bank registers, reused only between completed calls. -/
abbrev low0 : Fin 128 := 0
/-- Low helper result / argument register. -/
abbrev low1 : Fin 128 := 1
/-- Low helper power-base register. -/
abbrev low2 : Fin 128 := 2
/-- Low helper power-exponent register. -/
abbrev low3 : Fin 128 := 3
/-- Low residue input pointer. -/
abbrev low9 : Fin 128 := 9
/-- Low residue output pointer. -/
abbrev low10 : Fin 128 := 10
/-- Low residue length. -/
abbrev low11 : Fin 128 := 11
/-- Low signed modulus. -/
abbrev low12 : Fin 128 := 12
/-- First low Strassen matrix pointer. -/
abbrev low32 : Fin 128 := 32
/-- Second low Strassen matrix pointer. -/
abbrev low33 : Fin 128 := 33
/-- Low Strassen output pointer. -/
abbrev low34 : Fin 128 := 34
/-- Low Strassen scratch pointer. -/
abbrev low35 : Fin 128 := 35
/-- Low Strassen matrix depth. -/
abbrev low36 : Fin 128 := 36
/-- Low Strassen coefficient length. -/
abbrev low46 : Fin 128 := 46
/-- Original side length. -/
abbrev side : Fin 128 := 64
/-- Positive runtime modulus. -/
abbrev modulus : Fin 128 := 65
/-- Original canonical signed AB matrix. -/
abbrev inputAB : Fin 128 := 66
/-- Original canonical signed BC matrix, indexed by (b,c). -/
abbrev inputBC : Fin 128 := 67
/-- Original canonical signed AC matrix. -/
abbrev inputAC : Fin 128 := 68
/-- Beginning of caller-disjoint dirty workspace. -/
abbrev scratch : Fin 128 := 69
/-- Raw unsigned modular-zero count. -/
abbrev result : Fin 128 := 70
/-- Raw / canonical signed zero. -/
abbrev zero : Fin 128 := 71
/-- Raw unsigned one. -/
abbrev one : Fin 128 := 72
/-- Raw unsigned two, also the canonical signed word for one. -/
abbrev two : Fin 128 := 73
/-- Raw unsigned four. -/
abbrev four : Fin 128 := 74
/-- Actual computed ceiling binary logarithm of the side. -/
abbrev depth : Fin 128 := 75
/-- Padded power-of-two side. -/
abbrev paddedSide : Fin 128 := 76
/-- Original matrix word count. -/
abbrev cells : Fin 128 := 77
/-- Padded coefficient word count. -/
abbrev area : Fin 128 := 78
/-- First unsigned residue block. -/
abbrev residueAB : Fin 128 := 79
/-- Second unsigned residue block. -/
abbrev residueBC : Fin 128 := 80
/-- Third unsigned residue block. -/
abbrev residueAC : Fin 128 := 81
/-- Actually computed binary-to-base-four spread table. -/
abbrev spread : Fin 128 := 82
/-- First zero-padded monomial matrix. -/
abbrev matrixP : Fin 128 := 83
/-- Second zero-padded monomial matrix, with BC transposed. -/
abbrev matrixQ : Fin 128 := 84
/-- Actual signed-coefficient product. -/
abbrev matrixR : Fin 128 := 85
/-- Reused scalar/recursive multiplication scratch, followed by explicit frames. -/
abbrev productScratch : Fin 128 := 86
/-- Outer table, matrix or pair index. -/
abbrev index : Fin 128 := 87
/-- Inner coefficient index. -/
abbrev coefficient : Fin 128 := 88
/-- Computed row. -/
abbrev row : Fin 128 := 89
/-- Computed column. -/
abbrev column : Fin 128 := 90
/-- Computed Morton index. -/
abbrev position : Fin 128 := 91
/-- Spread of the current row. -/
abbrev rowSpread : Fin 128 := 92
/-- Spread of the current column. -/
abbrev columnSpread : Fin 128 := 93
/-- Base of one coefficient block. -/
abbrev block : Fin 128 := 94
/-- Actual unsigned residue, or the out-of-range padding sentinel p. -/
abbrev residue : Fin 128 := 95
/-- Actual indexed address. -/
abbrev address : Fin 128 := 96
/-- Arithmetic / loaded-word temporary. -/
abbrev temporary : Fin 128 := 97
/-- Canonical signed encoding of the positive modulus. -/
abbrev encodedModulus : Fin 128 := 98
/-- Current unsigned residue-array pointer. -/
abbrev residueSource : Fin 128 := 99
/-- Current coefficient-matrix pointer. -/
abbrev destination : Fin 128 := 100
/-- Number of padded matrix cells. -/
abbrev paddedCells : Fin 128 := 101

end Reg

/-- Real constant initialization and the existing native ceiling logarithm call. -/
@[expose] def logarithm : Code .standard 128 := ram[
  Reg.zero ← #0; Reg.one ← #1; Reg.two ← #2; Reg.four ← #4;
  Reg.low0 ← Reg.side; ⟪NatClog.program.rename (Fin.castLE (by decide))⟫;
  Reg.depth ← Reg.low1 ]

/-- Runtime powers, lengths and every actual workspace pointer. -/
@[expose] def layout : Code .standard 128 := ram[
  Reg.low2 ← Reg.two; Reg.low3 ← Reg.depth;
  ⟪Power.program.rename (Fin.castLE (by decide))⟫; Reg.paddedSide ← Reg.low0;
  Reg.cells ← Reg.side * Reg.side;
  Reg.paddedCells ← Reg.paddedSide * Reg.paddedSide;
  Reg.area ← Reg.paddedCells * Reg.modulus;
  Reg.encodedModulus ← Reg.modulus * Reg.two;
  Reg.residueAB ← Reg.scratch; Reg.residueBC ← Reg.residueAB + Reg.cells;
  Reg.residueAC ← Reg.residueBC + Reg.cells; Reg.spread ← Reg.residueAC + Reg.cells;
  Reg.matrixP ← Reg.spread + Reg.paddedSide; Reg.matrixQ ← Reg.matrixP + Reg.area;
  Reg.matrixR ← Reg.matrixQ + Reg.area; Reg.productScratch ← Reg.matrixR + Reg.area ]

/-- Call the existing actual signed-residue array loop on one original matrix. -/
@[expose] def residues (src dst : Fin 128) : Code .standard 128 :=
  .seq (ram[ Reg.low9 ← src; Reg.low10 ← dst; Reg.low11 ← Reg.cells;
    Reg.low12 ← Reg.encodedModulus ])
    (ThreeSum.ChanHe.Residues.program.rename (Fin.castLE (by decide)))

/-- Initialize the first actual spread-table word and its next unwritten index. -/
@[expose] def spreadSetup : Code .standard 128 := ram[
  Reg.address ← Reg.spread; *Reg.address ← Reg.zero; Reg.index ← #1 ]

/-- Compute one spread-table entry from its strictly earlier half-index entry. -/
@[expose] def spreadStep : Code .standard 128 := ram[
  Reg.temporary ← Reg.index / Reg.two; Reg.address ← Reg.spread + Reg.temporary;
  Reg.temporary ← *Reg.address; Reg.temporary ← Reg.temporary * Reg.four;
  Reg.position ← Reg.index % Reg.two; Reg.temporary ← Reg.temporary + Reg.position;
  Reg.address ← Reg.spread + Reg.index; *Reg.address ← Reg.temporary;
  Reg.index ← Reg.index + Reg.one ]

/-- Compute the whole spread table; no table is supplied by the caller. -/
@[expose] def spreadTable : Code .standard 128 :=
  .seq spreadSetup (.loop (.lt Reg.index Reg.paddedSide) spreadStep)

/-- Load actual row/column spread words and interleave their positions. -/
@[expose] def morton : Code .standard 128 := ram[
  Reg.address ← Reg.spread + Reg.row; Reg.rowSpread ← *Reg.address;
  Reg.address ← Reg.spread + Reg.column; Reg.columnSpread ← *Reg.address;
  Reg.position ← Reg.rowSpread * Reg.two; Reg.position ← Reg.position + Reg.columnSpread ]

/-- Compute the true row-major source position, with the actual BC transpose when requested. -/
@[expose] def readResidue (transpose : Bool) : Code .standard 128 :=
  .seq (if transpose then
      ram[ Reg.temporary ← Reg.column * Reg.side; Reg.temporary ← Reg.temporary + Reg.row ]
    else ram[ Reg.temporary ← Reg.row * Reg.side;
      Reg.temporary ← Reg.temporary + Reg.column ])
    (ram[ Reg.address ← Reg.residueSource + Reg.temporary; Reg.residue ← *Reg.address ])

/-- Store one actual canonical signed monomial coefficient and advance its index. -/
@[expose] def writeCoefficient : Code .standard 128 := ram[
  Reg.address ← Reg.block + Reg.coefficient;
  if Reg.coefficient = Reg.residue then [ *Reg.address ← Reg.two ]
  else [ *Reg.address ← Reg.zero ];
  Reg.coefficient ← Reg.coefficient + Reg.one ]

/-- Write one whole actual monomial coefficient block, including each padding zero. -/
@[expose] def writeCoefficients : Code .standard 128 :=
  .seq (ram[ Reg.coefficient ← #0 ])
    (.loop (.lt Reg.coefficient Reg.modulus) writeCoefficient)

/-- Guard the real residue read and use the out-of-range key p for every padded cell. -/
@[expose] def matrixResidue (transpose : Bool) : Code .standard 128 := ram[
  if Reg.row < Reg.side then [
    if Reg.column < Reg.side then [ ⟪readResidue transpose⟫ ]
    else [ Reg.residue ← Reg.modulus ] ]
  else [ Reg.residue ← Reg.modulus ] ]

/-- One real padded matrix cell: compute coordinates/Morton address, select the admitted
residue or padding sentinel, write every coefficient, and advance the original cell index. -/
@[expose] def matrixStep (transpose : Bool) : Code .standard 128 :=
  .seq (ram[ Reg.row ← Reg.index / Reg.paddedSide;
    Reg.column ← Reg.index % Reg.paddedSide ])
    (.seq morton (.seq (ram[ Reg.block ← Reg.position * Reg.modulus;
      Reg.block ← Reg.destination + Reg.block ])
      (.seq (matrixResidue transpose) (.seq writeCoefficients
        (ram[ Reg.index ← Reg.index + Reg.one ])))))

/-- Create a complete zero-padded cyclic matrix from real residue words. -/
@[expose] def matrix (src dst : Fin 128) (transpose : Bool) : Code .standard 128 := ram[
  Reg.residueSource ← src; Reg.destination ← dst; Reg.index ← #0;
  while Reg.index < Reg.paddedCells do [ ⟪matrixStep transpose⟫ ] ]

/-- Invoke the actual fixed Strassen controller in the low 64-register bank. -/
@[expose] def product : Code .standard 128 := ram[
  Reg.low32 ← Reg.matrixP; Reg.low33 ← Reg.matrixQ; Reg.low34 ← Reg.matrixR;
  Reg.low35 ← Reg.productScratch; Reg.low36 ← Reg.depth; Reg.low46 ← Reg.modulus;
  ⟪Strassen.program.rename (Fin.castLE (by decide))⟫ ]

/-- One actual selected-coefficient read and unsigned count accumulation. -/
@[expose] def countStep : Code .standard 128 :=
  .seq (ram[ Reg.row ← Reg.index / Reg.side; Reg.column ← Reg.index % Reg.side ])
    (.seq morton (.seq (ram[
      Reg.address ← Reg.residueAB + Reg.index; Reg.residue ← *Reg.address;
      if Reg.residue = Reg.zero then [ Reg.residue ← #0 ]
      else [ Reg.residue ← Reg.modulus - Reg.residue ] ])
      (ram[ Reg.block ← Reg.position * Reg.modulus;
        Reg.address ← Reg.matrixR + Reg.block; Reg.address ← Reg.address + Reg.residue;
        Reg.temporary ← *Reg.address; Reg.temporary ← Reg.temporary / Reg.two;
        Reg.result ← Reg.result + Reg.temporary; Reg.index ← Reg.index + Reg.one ])))

/-- Read and add exactly one coefficient for each original AB pair. -/
@[expose] def count : Code .standard 128 := ram[
  Reg.result ← #0; Reg.index ← #0;
  while Reg.index < Reg.cells do [ ⟪countStep⟫ ] ]

/-- Concrete runtime-parameter counter; every multiplication is actual native code. -/
@[expose] def program : Code .standard 128 := ram[
  ⟪logarithm⟫; ⟪layout⟫;
  ⟪residues Reg.inputAB Reg.residueAB⟫; ⟪residues Reg.inputBC Reg.residueBC⟫;
  ⟪residues Reg.inputAC Reg.residueAC⟫; ⟪spreadTable⟫;
  ⟪matrix Reg.residueAC Reg.matrixP false⟫; ⟪matrix Reg.residueBC Reg.matrixQ true⟫;
  ⟪product⟫; ⟪count⟫ ]

/-- Ordinary initialized input: raw `(n,p)`, followed by the three canonical signed arrays. -/
@[expose] def input : Code .standard 128 := ram[
  Reg.address ← #1; Reg.side ← *Reg.address; Reg.address ← #2; Reg.modulus ← *Reg.address;
  Reg.cells ← Reg.side * Reg.side; Reg.inputAB ← #3;
  Reg.inputBC ← Reg.inputAB + Reg.cells; Reg.inputAC ← Reg.inputBC + Reg.cells;
  Reg.scratch ← Reg.inputAC + Reg.cells ]

/-- Fixed initialized counter code, independent of dimensions, modulus and physical width. -/
@[expose] def entryProgram : Code .standard 128 := .seq input program

/-- The complete counter is one finite standard native program with no word-width reads. -/
theorem program_fixed : (entryProgram.program Reg.result).length ≤ 32768 ∧
    ¬(entryProgram.program Reg.result).ReadsWidth := by
  constructor
  · decide +kernel
  · apply Code.not_readsWidth_program
    decide +kernel

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
