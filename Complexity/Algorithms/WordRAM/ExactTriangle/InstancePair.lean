/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.WriteMatrices
import Mathlib.Tactic.FinCases

/-!
# Native matrix pairs and instance records

One call writes a six-word record `(rho,piece,queries,count,X,Y)` and the actual raw unsigned
zero/one matrices `X : n×D` and `Y : D×n` immediately after it. Both matrices reuse
`WriteMatrices.program`; all pointer arithmetic, argument delivery and record stores are charged.
The query words remain in the earlier computed catalogue and are shared by reference.

`setup`, `writeHeader`, `deliverLeft`, `deliverRight` and `matrix` are internal program stages.
They are exposed so that the complete catalogue controller can reuse the same fixed program.

## Main definitions

* `InstancePair.program`: fixed thirty-two-register matrix-pair and record writer.
* `InstancePair.leftArgs`, `InstancePair.rightArgs`: existing matrix-writer arguments read
  directly from the runtime registers.

## Main results

* `InstancePair.exec`: both exact matrices and the real record, with a combined outside frame
  and a `40nD+38` charged instruction bound before halt.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.InstancePair

open Cslib.WordRAM

/-- Computed A–C residue-array pointer. -/
abbrev srcLeft : Fin 32 := 17
/-- Computed B–C residue-array pointer. -/
abbrev srcRight : Fin 32 := 18
/-- First word of the instance record. -/
abbrev base : Fin 32 := 19
/-- Outer matrix dimension. -/
abbrev size : Fin 32 := 20
/-- Padded middle matrix dimension. -/
abbrev dimension : Fin 32 := 21
/-- Positive residue modulus. -/
abbrev modulus : Fin 32 := 22
/-- First original vertex in the piece. -/
abbrev first : Fin 32 := 23
/-- Actual number of vertices in the piece. -/
abbrev length : Fin 32 := 24
/-- Query residue. -/
abbrev rho : Fin 32 := 25
/-- Actual query-pair pointer. -/
abbrev queries : Fin 32 := 26
/-- Actual number of query pairs. -/
abbrev count : Fin 32 := 27
/-- Index of the original piece. -/
abbrev piece : Fin 32 := 28
/-- Constant one, preserved by both matrix calls. -/
abbrev one : Fin 32 := 29
/-- Header cursor. -/
abbrev addr : Fin 32 := 30
/-- Number of words in one matrix. -/
abbrev area : Fin 32 := 31

/-- Existing left-matrix arguments, with its output following the six-word record. -/
@[expose]
def leftArgs (x : Data 32) : WriteMatrices.Args where
  src := x.regs srcLeft
  dst := x.regs base + 6
  n := x.regs size
  D := x.regs dimension
  p := x.regs modulus
  first := x.regs first
  length := x.regs length
  rho := x.regs rho

/-- Existing right-matrix arguments, immediately following the left matrix. -/
@[expose]
def rightArgs (x : Data 32) : WriteMatrices.Args :=
  { leftArgs x with
    src := x.regs srcRight
    dst := x.regs base + 6 + x.regs size * x.regs dimension }

/-- Compute the left output pointer and matrix area with native arithmetic. -/
@[expose]
def setup : Code .standard 32 :=
  let dst : Fin 32 := 1
  ram[ one ← #1; addr ← #6; dst ← base + addr; area ← size * dimension ]

/-- Write the actual query reference and both computed matrix pointers. -/
@[expose]
def writeHeader : Code .standard 32 :=
  let dst : Fin 32 := 1
  let scratch : Fin 32 := 0
  ram[ addr ← base; *addr ← rho; addr ← addr + one; *addr ← piece;
    addr ← addr + one; *addr ← queries; addr ← addr + one; *addr ← count;
    addr ← addr + one; *addr ← dst; addr ← addr + one;
    scratch ← dst + area; *addr ← scratch ]

/-- Deliver the seven remaining left-matrix arguments; its destination is already computed. -/
@[expose]
def deliverLeft : Code .standard 32 :=
  let src : Fin 32 := 0
  let n : Fin 32 := 2
  let D : Fin 32 := 3
  let p : Fin 32 := 4
  let start : Fin 32 := 5
  let len : Fin 32 := 6
  let residue : Fin 32 := 7
  ram[ src ← srcLeft; n ← size; D ← dimension; p ← modulus;
    start ← first; len ← length; residue ← rho ]

/-- The left writer preserves its argument registers, so only the source and output pointer
change for the right call. -/
@[expose]
def deliverRight : Code .standard 32 :=
  let src : Fin 32 := 0
  let dst : Fin 32 := 1
  ram[ src ← srcRight; dst ← dst + area ]

/-- Reuse either native matrix writer in the lower seventeen registers. -/
@[expose]
def matrix (side : Bool) : Code .standard 32 :=
  (WriteMatrices.program side).rename (Fin.castLE (by decide))

/-- Complete record and matrix-pair construction. -/
@[expose]
def program : Code .standard 32 :=
  .seq (.seq setup writeHeader) (.seq deliverLeft (.seq (matrix false)
    (.seq deliverRight (matrix true))))

/-- Finite code independent of every runtime dimension and physical width. -/
theorem program_fixed : program.size ≤ 160 ∧ ¬program.ReadsWidth := by decide

private abbrev bank : Fin 17 → Fin 32 := Fin.castLE (by decide)

private theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

private theorem header_preserves : ∀ i : Fin 32,
    17 ≤ i.val → i.val < 29 → (Code.seq setup writeHeader).Preserves i := by decide

private theorem matrix_preserves (side : Bool) : ∀ i : Fin 32,
    17 ≤ i.val → (matrix side).Preserves i := by cases side <;> decide

/-- Six raw unsigned record words: residue, piece index, shared query pointer/count, then the
two computed matrix pointers. Matrix entries themselves are raw zero/one words. -/
@[expose]
def recordWords (x : Data 32) : Fin 6 → ℕ :=
  ![x.regs rho, x.regs piece, x.regs queries, x.regs count, (leftArgs x).dst, (rightArgs x).dst]

private theorem exec_header {w : ℕ} (x : Data 32)
    (hfit : Fits w (x.regs base + 6 + 2 * (x.regs size * x.regs dimension) + 7)) :
    ∃ y, ExecWithin w (.seq setup writeHeader) x y 17 ∧
      y.regs 1 = x.regs base + 6 ∧ y.regs area = x.regs size * x.regs dimension ∧
      (∀ i : Fin 32, 17 ≤ i.val → i.val < 29 → y.regs i = x.regs i) ∧
      (Block.mk (x.regs base) 6).Realizes y.mem (recordWords x) ∧
      (∀ a, ¬(x.regs base ≤ a ∧ a < x.regs base + 6) → y.mem a = x.mem a) := by
  let b := x.regs base
  let M := x.regs size * x.regs dimension
  let a := x.set one 1 |>.set addr 6 |>.set 1 (b + 6) |>.set area M
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h6 : Fits w 6 := hfit.of_le (by omega)
  have hb6 : Fits w (x.regs base + 6) := hfit.of_le (by omega)
  have hM : Fits w (x.regs size * x.regs dimension) := hfit.of_le (by omega)
  have hsetup : ExecWithin w setup x a 4 := by
    ram_eval [setup, a, b, M, one, addr, base, area, size, dimension, h1, h6, hb6, hM,
      Fin.mk.injEq]
  let y := a.set addr b |>.write b (x.regs rho)
    |>.set addr (b + 1) |>.write (b + 1) (x.regs piece)
    |>.set addr (b + 2) |>.write (b + 2) (x.regs queries)
    |>.set addr (b + 3) |>.write (b + 3) (x.regs count)
    |>.set addr (b + 4) |>.write (b + 4) (b + 6)
    |>.set addr (b + 5) |>.set 0 (b + 6 + M) |>.write (b + 5) (b + 6 + M)
  have hb1 : Fits w (b + 1) := hfit.of_le (by dsimp [b]; omega)
  have hb2 : Fits w (b + 1 + 1) := hfit.of_le (by dsimp [b]; omega)
  have hb3 : Fits w (b + 1 + 1 + 1) := hfit.of_le (by dsimp [b]; omega)
  have hb4 : Fits w (b + 1 + 1 + 1 + 1) := hfit.of_le (by dsimp [b]; omega)
  have hb5 : Fits w (b + 1 + 1 + 1 + 1 + 1) := hfit.of_le (by dsimp [b]; omega)
  have hbM : Fits w (b + 6 + M) := hfit.of_le (by dsimp [b, M]; omega)
  have hheader : ExecWithin w writeHeader a y 13 := by
    ram_eval [writeHeader, y, a, b, M, one, addr, base, area, rho, piece, queries, count,
      hb1, hb2, hb3, hb4, hb5, hbM, Fin.mk.injEq]
  refine ⟨y, hsetup.seq hheader, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [y, a, b, addr, area, one]
  · simp +decide [y, a, M, addr, area]
  · intro i hi hi'
    exact (hsetup.seq hheader).regs_eq (header_preserves i hi hi')
  · intro i
    fin_cases i <;>
      simp [Block.read, recordWords, leftArgs, rightArgs, y, a, b, M]
  · intro j hj
    simp only [y, a, Data.set_mem, Data.write_mem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- Write both actual matrices and their shared-query instance record. The source arrays are
ordinary residue words before the output region. Existing `WriteMatrices.entry` supplies the
semantics; no adjacency array, execution or time contract is an input. Halt is excluded. -/
theorem exec {w : ℕ} (x : Data 32) (L R : ℕ → ℕ)
    (hrho : x.regs rho < x.regs modulus)
    (hpiece : x.regs first + x.regs length ≤ x.regs size)
    (hL : ∀ i < x.regs size * x.regs size, L i < x.regs modulus)
    (hR : ∀ i < x.regs size * x.regs size, R i < x.regs modulus)
    (hleft : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcLeft + i) = L i)
    (hright : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcRight + i) = R i)
    (hsL : x.regs srcLeft + x.regs size * x.regs size ≤ x.regs base)
    (hsR : x.regs srcRight + x.regs size * x.regs size ≤ x.regs base)
    (hfit : Fits w (x.regs base + 6 + 2 * (x.regs size * x.regs dimension) +
      x.regs srcLeft + x.regs srcRight + 2 * (x.regs size * x.regs size) +
        2 * x.regs modulus + 7)) :
    ∃ y, ExecWithin w program x y (40 * (x.regs size * x.regs dimension) + 38) ∧
      (Block.mk (x.regs base) 6).Realizes y.mem (recordWords x) ∧
      (Block.mk (leftArgs x).dst (x.regs size * x.regs dimension)).Realizes y.mem
        (fun i => WriteMatrices.entry false (leftArgs x) L i) ∧
      (Block.mk (rightArgs x).dst (x.regs size * x.regs dimension)).Realizes y.mem
        (fun i => WriteMatrices.entry true (rightArgs x) R i) ∧
      (∀ a, ¬(x.regs base ≤ a ∧
        a < x.regs base + 6 + 2 * (x.regs size * x.regs dimension)) → y.mem a = x.mem a) := by
  let M := x.regs size * x.regs dimension
  let A := leftArgs x
  let B := rightArgs x
  obtain ⟨a, ha, ha1, haM, hameta, harecord, haframe⟩ := exec_header x
    (hfit.of_le (by omega))
  have har (i : Fin 32) (hi : 17 ≤ i.val ∧ i.val < 29) : a.regs i = x.regs i :=
    hameta i hi.1 hi.2
  let b := a.set 0 (x.regs srcLeft) |>.set 2 (x.regs size) |>.set 3 (x.regs dimension)
    |>.set 4 (x.regs modulus) |>.set 5 (x.regs first) |>.set 6 (x.regs length)
    |>.set 7 (x.regs rho)
  have hb : ExecWithin w deliverLeft a b 7 := by
    have hsrc := har srcLeft (by decide)
    have hn := har size (by decide)
    have hD := har dimension (by decide)
    have hp := har modulus (by decide)
    have hfirst := har first (by decide)
    have hlen := har length (by decide)
    have hr := har rho (by decide)
    ram_eval [deliverLeft, b, hsrc, hn, hD, hp, hfirst, hlen, hr, srcLeft, size,
      dimension, modulus, first, length, rho, Fin.mk.injEq]
  have hbEntry : WriteMatrices.Entry A (b.comap bank) := by
    constructor <;>
      simp +decide [A, leftArgs, b, bank, WriteMatrices.src, WriteMatrices.dst,
        WriteMatrices.size, WriteMatrices.dimension, WriteMatrices.modulus, WriteMatrices.first,
        WriteMatrices.length, WriteMatrices.rho, ha1]
  obtain ⟨v, hv, hvEntry, -, hvleft, hvframe⟩ := WriteMatrices.exec false A L (b.comap bank)
    hbEntry hrho hpiece hL
    (by
      intro i hi
      change a.mem (x.regs srcLeft + i) = L i
      rw [haframe _ (by dsimp [A, leftArgs] at hi; omega)]
      exact hleft i hi)
    (hfit.of_le (by dsimp [A, leftArgs]; omega))
    (hfit.of_le (by dsimp [A, leftArgs]; omega))
    (hfit.of_le (by dsimp [A, leftArgs]; omega))
    (by dsimp [A, leftArgs]; omega)
  let c := v.extend bank b
  have hc : ExecWithin w (matrix false) b c (20 * M + 6) := by
    simpa only [matrix, c, A, leftArgs, M] using hv.rename bank_injective
  have hcEntry : WriteMatrices.Entry A (c.comap bank) := by
    simpa only [c, Data.comap_extend bank_injective] using hvEntry
  have hc1 : c.regs 1 = A.dst := hcEntry.dst
  have hcM : c.regs area = M :=
    (hc.regs_eq (matrix_preserves false area (by decide))).trans (by
      simpa +decide [b, area, M] using haM)
  have hcRight : c.regs srcRight = x.regs srcRight :=
    (hc.regs_eq (matrix_preserves false srcRight (by decide))).trans (by
      simpa +decide [b, srcRight] using har srcRight (by decide))
  have hcframe (j : ℕ) (hj : ¬(Block.mk A.dst M).Owns j) : c.mem j = a.mem j :=
    hvframe j hj
  let d := c.set 0 (x.regs srcRight) |>.set 1 (A.dst + M)
  have hrightDst : Fits w (A.dst + M) := hfit.of_le (by dsimp [A, leftArgs, M]; omega)
  have hd : ExecWithin w deliverRight c d 2 := by
    ram_eval [deliverRight, d, hcRight, hc1, hcM, hrightDst, srcRight, area, Fin.mk.injEq]
  have hdEntry : WriteMatrices.Entry B (d.comap bank) := by
    constructor
    · simp +decide [d, B, rightArgs, bank, WriteMatrices.src]
    · simp +decide [d, B, rightArgs, A, leftArgs, M, bank, WriteMatrices.dst]
    · simpa +decide [d, B, rightArgs, bank, WriteMatrices.size] using hcEntry.size
    · simpa +decide [d, B, rightArgs, bank, WriteMatrices.dimension] using hcEntry.dimension
    · simpa +decide [d, B, rightArgs, bank, WriteMatrices.modulus] using hcEntry.modulus
    · simpa +decide [d, B, rightArgs, bank, WriteMatrices.first] using hcEntry.first
    · simpa +decide [d, B, rightArgs, bank, WriteMatrices.length] using hcEntry.length
    · simpa +decide [d, B, rightArgs, bank, WriteMatrices.rho] using hcEntry.rho
  obtain ⟨z, hz, -, -, hzright, hzframe⟩ := WriteMatrices.exec true B R (d.comap bank)
    hdEntry hrho hpiece hR
    (by
      intro i hi
      change c.mem (x.regs srcRight + i) = R i
      rw [hcframe _ (by
        dsimp [Block.Owns, A, leftArgs, M]
        dsimp [B, rightArgs, leftArgs] at hi
        omega),
        haframe _ (by dsimp [B, rightArgs, leftArgs] at hi; omega)]
      exact hright i hi)
    (hfit.of_le (by dsimp [B, rightArgs, leftArgs]; omega))
    (hfit.of_le (by dsimp [B, rightArgs, leftArgs]; omega))
    (hfit.of_le (by dsimp [B, rightArgs, leftArgs]; omega))
    (by dsimp [B, rightArgs, leftArgs]; omega)
  let y := z.extend bank d
  have hy : ExecWithin w (matrix true) d y (20 * M + 6) := by
    simpa only [matrix, y, B, rightArgs, leftArgs, M] using hz.rename bank_injective
  have hyframe (j : ℕ) (hj : ¬(Block.mk B.dst M).Owns j) : y.mem j = c.mem j :=
    hzframe j hj
  refine ⟨y, ?_, ?_, ?_, hzright, ?_⟩
  · convert ha.seq (hb.seq (hc.seq (hd.seq hy))) using 1
    · rfl
    · dsimp [M]
      omega
  · intro i
    change y.mem (x.regs base + i.val) = recordWords x i
    rw [hyframe _ (by
        dsimp [Block.Owns, B, rightArgs, leftArgs]
        have hi : i.val < 6 := i.isLt
        omega),
      hcframe _ (by
        dsimp [Block.Owns, A, leftArgs]
        have hi : i.val < 6 := i.isLt
        omega)]
    exact harecord i
  · intro i
    change y.mem (A.dst + i.val) = WriteMatrices.entry false A L i
    rw [hyframe _ (by
      dsimp [Block.Owns, B, rightArgs, leftArgs, A]
      have hi := i.isLt
      dsimp [M] at hi
      omega)]
    exact hvleft i
  · intro j hj
    rw [hyframe _ (by dsimp [Block.Owns, B, rightArgs, leftArgs, M]; omega),
      hcframe _ (by dsimp [Block.Owns, A, leftArgs, M]; omega), haframe _ (by omega)]

end Cslib.Algorithms.WordRAM.ExactTriangle.InstancePair
