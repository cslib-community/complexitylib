/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Catalogue
public import Complexity.Algorithms.WordRAM.ExactTriangle.InstancePair
import Mathlib.Tactic.FinCases

/-!
# Native ExactTriangle instance preparation

The input header is `(D,g,n,p)`, followed by the three signed weight matrices. The program first
computes the real class/chunk catalogue. It then visits each actual chunk and piece, reads that
chunk's descriptor, computes the piece boundaries and writes its record and two zero/one matrices.
The records share the already computed query arrays. Every visit uses the existing native
`InstancePair.program` rather than assuming a matrix-preparation routine.

The output records and matrices occupy consecutive variable-size blocks. Register `output` names
the first record, `produced` gives their actual number and `heap` is their final allocation end.
Each block has six record words followed by `2nD` matrix words. This module prepares instances;
it does not choose a prime, evaluate their queried products or decide ExactTriangle.

## Main definitions

* `Instances.program`: fixed sixty-four-register initialized instance-preparation program.
* `Instances.visit`: one computed class/chunk/piece visit, including both native matrix calls.
* `Instances.timeBound`: the catalogue cost plus the full native visit and loop budgets,
  including the final halt.
* `Instances.Output`: actual catalogue, record, matrix and frame readback.

## Main results

* `Instances.exec_at`: complete native execution from the original header and weight arrays.

`PreparationInput` supplies the initialized flat-program interface and derived width bounds;
`PreparationBounds` proves the preparation time bound in the source's parameter regime.
Code-stage definitions are exposed for kernel-checked interpreter clients.
Proof helpers are private.

## References

The matrix geometry follows the pinned
[Theorem 17 matrix construction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean).
The native controller and resource proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Instances

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Outer matrix dimension. -/
abbrev size : Fin 64 := 32
/-- Target padded middle dimension. -/
abbrev dimension : Fin 64 := 33
/-- Residue modulus. -/
abbrev modulus : Fin 64 := 34
/-- Computed maximum vertices per piece. -/
abbrev pieceLength : Fin 64 := 35
/-- Computed number of pieces. -/
abbrev pieces : Fin 64 := 36
/-- Actual number of nonempty query chunks. -/
abbrev chunks : Fin 64 := 37
/-- Computed chunk-descriptor array. -/
abbrev descriptors : Fin 64 := 38
/-- First output record. -/
abbrev output : Fin 64 := 39
/-- Number of completely written instance blocks. -/
abbrev produced : Fin 64 := 40
/-- Actual chunk count times piece count. -/
abbrev total : Fin 64 := 41
/-- Next free output record. -/
abbrev heap : Fin 64 := 42
/-- Words per record and its two matrices. -/
abbrev stride : Fin 64 := 43
/-- Constant one. -/
abbrev one : Fin 64 := 44
/-- Words per chunk descriptor. -/
abbrev three : Fin 64 := 45
/-- Words per instance record. -/
abbrev six : Fin 64 := 46
/-- Words in one matrix. -/
abbrev area : Fin 64 := 47
/-- Original A–C residue matrix. -/
abbrev srcLeft : Fin 64 := 48
/-- Original B–C residue matrix. -/
abbrev srcRight : Fin 64 := 49
/-- Descriptor/header address temporary. -/
abbrev addr : Fin 64 := 50
/-- Current chunk ordinal. -/
abbrev chunkIndex : Fin 64 := 51
/-- Current piece ordinal. -/
abbrev pieceIndex : Fin 64 := 52
/-- Residue loaded from the actual chunk descriptor. -/
abbrev rho : Fin 64 := 53
/-- Query pointer loaded from the actual chunk descriptor. -/
abbrev queries : Fin 64 := 54
/-- Query count loaded from the actual chunk descriptor. -/
abbrev queryCount : Fin 64 := 55
/-- First vertex of the current piece. -/
abbrev first : Fin 64 := 56
/-- Actual length of the current piece. -/
abbrev length : Fin 64 := 57
/-- Original weight-matrix area temporary. -/
abbrev temp : Fin 64 := 58

/-- Existing catalogue computation in the lower thirty-two registers. -/
@[expose]
def catalogue : Code .standard 64 := Catalogue.program.rename (Fin.castLE (by decide))

/-- Save the actual catalogue outputs and compute the allocation stride and residue bases. -/
@[expose]
def setup : Code .standard 64 :=
  let lowSize : Fin 64 := 16
  let lowModulus : Fin 64 := 17
  let lowLength : Fin 64 := 28
  let lowPieces : Fin 64 := 29
  let lowChunks : Fin 64 := 21
  let lowDescriptors : Fin 64 := 18
  let lowOutput : Fin 64 := 22
  ram[ one ← #1; three ← #3; six ← #6;
    size ← lowSize; modulus ← lowModulus; pieceLength ← lowLength; pieces ← lowPieces;
    chunks ← lowChunks; descriptors ← lowDescriptors; output ← lowOutput;
    produced ← #0; heap ← output; total ← chunks * pieces;
    addr ← #1; dimension ← *addr; area ← size * dimension;
    stride ← area + area; stride ← stride + six;
    temp ← size * size; srcLeft ← temp + temp; srcLeft ← srcLeft + temp;
    srcRight ← srcLeft + temp; srcLeft ← srcRight + temp; addr ← #5;
    srcLeft ← srcLeft + addr; srcRight ← srcRight + addr ]

/-- Compute the chunk and piece ordinals, then load the real query reference and piece bounds. -/
@[expose]
def select : Code .standard 64 := ram[
  chunkIndex ← produced / pieces; pieceIndex ← produced % pieces;
  addr ← chunkIndex * three; addr ← addr + descriptors; rho ← *addr;
  addr ← addr + one; queries ← *addr; addr ← addr + one; queryCount ← *addr;
  first ← pieceIndex * pieceLength; length ← size - first;
  if pieceLength < length then [ length ← pieceLength ] else [ length ← length ] ]

/-- Deliver every actual pointer, coordinate and count to the existing instance-pair ABI. -/
@[expose]
def deliver : Code .standard 64 :=
  let pairLeft : Fin 64 := 17
  let pairRight : Fin 64 := 18
  let pairBase : Fin 64 := 19
  let pairSize : Fin 64 := 20
  let pairDimension : Fin 64 := 21
  let pairModulus : Fin 64 := 22
  let pairFirst : Fin 64 := 23
  let pairLength : Fin 64 := 24
  let pairRho : Fin 64 := 25
  let pairQueries : Fin 64 := 26
  let pairCount : Fin 64 := 27
  let pairPiece : Fin 64 := 28
  ram[ pairLeft ← srcLeft; pairRight ← srcRight; pairBase ← heap; pairSize ← size;
    pairDimension ← dimension; pairModulus ← modulus; pairFirst ← first; pairLength ← length;
    pairRho ← rho; pairQueries ← queries; pairCount ← queryCount; pairPiece ← pieceIndex ]

/-- Existing native record and matrix-pair writer. -/
@[expose]
def pair : Code .standard 64 := InstancePair.program.rename (Fin.castLE (by decide))

/-- Advance only after the complete pair has been written. -/
@[expose]
def advance : Code .standard 64 := ram[ heap ← heap + stride; produced ← produced + one ]

/-- One actual instance; every selection, argument-delivery and matrix instruction is native. -/
@[expose]
def visit : Code .standard 64 := .seq select (.seq deliver (.seq pair advance))

/-- Prepare every actual chunk/piece pair after computing the catalogue. -/
@[expose]
def program : Code .standard 64 :=
  .seq catalogue (.seq setup (.loop (.lt produced total) visit))

/-- The catalogue prefix, twenty-six setup instructions, each `40nD+66` visit and its two loop
instructions, the two loop-exit instructions and the final halt are accounted separately. -/
@[expose]
def timeBound (n D p K H : ℕ) : ℕ :=
  Catalogue.cost n D p + K * H * (40 * (n * D) + 68) + 29

/-- Original-header bound for all arithmetic and allocated addresses. The conservative maximum
`p*n²` chunk count and `n` pieces cover every actual catalogue entry. Signed weights have their
separate magnitude fit premise; no layout information is supplied by the caller. -/
@[expose]
def budget (n D g p : ℕ) : ℕ :=
  let N := n * n
  let K := p * N
  let out := 5 + 6 * N + p + 2 * N * p + 3 * K
  Catalogue.budget n D g p + 2 * out + (K * n) * (6 + 2 * (n * D)) +
    20 * N + 3 * p + 4 * n + 2 * (n * D) + K * n + 64

private theorem parameter_bounds {n D g : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n)
    (hg : 1 ≤ g) :
    0 < pieceSize D g ∧ pieceSize D g ≤ n ∧
      0 < numPieces n D g ∧ numPieces n D g ≤ n ∧
      ∀ j < numPieces n D g, j * pieceSize D g ≤ n := by
  have hs : 0 < sOf D := by
    change 0 < Nat.sqrt D
    exact Nat.sqrt_pos.mpr hD
  have hc := Nat.le_ceilDiv_mul (a := sOf D) (by omega : 0 < g)
  have hB : 0 < pieceSize D g := by
    change sOf D ≤ pieceSize D g * g at hc
    by_contra h
    have : pieceSize D g = 0 := by omega
    rw [this, Nat.zero_mul] at hc
    omega
  have hBn : pieceSize D g ≤ n :=
    (pieceSize_le_sOf hg).trans ((Nat.sqrt_le_self D).trans hDn)
  have hcover : n ≤ numPieces n D g * pieceSize D g := Nat.le_ceilDiv_mul hB
  have hH : 0 < numPieces n D g := by
    by_contra h
    have : numPieces n D g = 0 := by omega
    rw [this, Nat.zero_mul] at hcover
    omega
  have hHn : numPieces n D g ≤ n :=
    (Nat.ceilDiv_le_iff hB).mpr (Nat.le_mul_of_pos_right n hB)
  refine ⟨hB, hBn, hH, hHn, fun j hj => ?_⟩
  have hover : numPieces n D g * pieceSize D g < n + pieceSize D g :=
    Nat.ceilDiv_mul_lt hB
  have hstep := Nat.mul_le_mul_right (pieceSize D g) (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at hstep
  omega

/-- One bounded instruction graph with no word-size reads. -/
theorem program_fixed : program.size ≤ 640 ∧ ¬program.ReadsWidth := by decide

private theorem select_preserves : ∀ i : Fin 64, i.val < 50 → select.Preserves i := by decide

private theorem visit_preserves : ∀ i : Fin 64,
    (32 ≤ i.val ∧ i.val < 50 ∧ i ≠ heap ∧ i ≠ produced) → visit.Preserves i := by decide

private theorem prefix_preserves : ∀ i : Fin 64, 32 ≤ i.val → i.val < 50 →
    (Code.seq select (.seq deliver pair)).Preserves i := by decide

private abbrev pairBank : Fin 32 → Fin 64 := Fin.castLE (by decide)

private theorem budget_covers_setup {n D g p K H : ℕ}
    (hK : K ≤ p * (n * n)) (hH : H ≤ n) :
    5 * (n * n) + 2 * (n * D) + K * H +
      (5 + 6 * (n * n) + p + 2 * (n * n) * p + 3 * K) + 8 ≤ budget n D g p := by
  have hT := Nat.mul_le_mul hK hH
  dsimp only [budget]
  omega

private theorem budget_covers_loop {n D g p K H B : ℕ}
    (hK : K ≤ p * (n * n)) (hH : H ≤ n) (hHB : H * B ≤ n * n) :
    2 * (5 + 6 * (n * n) + p + 2 * (n * n) * p + 3 * K) +
      K * H * (6 + 2 * (n * D)) + 11 * (n * n) + 2 * p + n + H + H * B + K * H + 26 ≤
        budget n D g p := by
  have hT := Nat.mul_le_mul hK hH
  have hTS := Nat.mul_le_mul_right (6 + 2 * (n * D)) hT
  dsimp only [budget]
  omega

private theorem exec_setup {w : ℕ} (x : Data 64) (n D p B H K desc out : ℕ)
    (hn : x.regs 16 = n) (hp : x.regs 17 = p) (hB : x.regs 28 = B)
    (hH : x.regs 29 = H) (hK : x.regs 21 = K) (hd : x.regs 18 = desc)
    (hout : x.regs 22 = out) (hD : x.mem 1 = D)
    (hfit : Fits w (5 * (n * n) + 2 * (n * D) + K * H + out + 8)) :
    ∃ y, ExecWithin w setup x y 26 ∧ y.mem = x.mem ∧
      y.regs size = n ∧ y.regs dimension = D ∧ y.regs modulus = p ∧
      y.regs pieceLength = B ∧ y.regs pieces = H ∧ y.regs chunks = K ∧
      y.regs descriptors = desc ∧ y.regs output = out ∧ y.regs produced = 0 ∧
      y.regs total = K * H ∧ y.regs heap = out ∧ y.regs stride = 6 + 2 * (n * D) ∧
      y.regs one = 1 ∧ y.regs three = 3 ∧
      y.regs srcLeft = 5 + 5 * (n * n) ∧ y.regs srcRight = 5 + 4 * (n * n) := by
  let N := n * n
  let M := n * D
  let y := x.set one 1 |>.set three 3 |>.set six 6
    |>.set size n |>.set modulus p |>.set pieceLength B |>.set pieces H
    |>.set chunks K |>.set descriptors desc |>.set output out
    |>.set produced 0 |>.set heap out |>.set total (K * H)
    |>.set addr 1 |>.set dimension D |>.set area M
    |>.set stride (M + M) |>.set stride (M + M + 6)
    |>.set temp N |>.set srcLeft (N + N) |>.set srcLeft (N + N + N)
    |>.set srcRight (N + N + N + N) |>.set srcLeft (N + N + N + N + N)
    |>.set addr 5 |>.set srcLeft (N + N + N + N + N + 5)
    |>.set srcRight (N + N + N + N + 5)
  have h0 : Fits w 0 := hfit.of_le (by omega)
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h3 : Fits w 3 := hfit.of_le (by omega)
  have h5 : Fits w 5 := hfit.of_le (by omega)
  have h6 : Fits w 6 := hfit.of_le (by omega)
  have hT : Fits w (K * H) := hfit.of_le (by omega)
  have hN : Fits w N := hfit.of_le (by dsimp [N]; omega)
  have h2N : Fits w (N + N) := hfit.of_le (by dsimp [N]; omega)
  have h3N : Fits w (N + N + N) := hfit.of_le (by dsimp [N]; omega)
  have h4N : Fits w (N + N + N + N) := hfit.of_le (by dsimp [N]; omega)
  have h5N : Fits w (N + N + N + N + N) := hfit.of_le (by dsimp [N]; omega)
  have h4N5 : Fits w (N + N + N + N + 5) := hfit.of_le (by dsimp [N]; omega)
  have h5N5 : Fits w (N + N + N + N + N + 5) := hfit.of_le (by dsimp [N]; omega)
  have hM : Fits w M := hfit.of_le (by dsimp [M]; omega)
  have h2M : Fits w (M + M) := hfit.of_le (by dsimp [M]; omega)
  have hstride : Fits w (M + M + 6) := hfit.of_le (by dsimp [M]; omega)
  refine ⟨y, ?_, rfl, ?_⟩
  · ram_eval [setup, y, hn, hp, hB, hH, hK, hd, hout, hD, h0, h1, h3, h5, h6,
      hT, hN, h2N, h3N, h4N, h5N, h4N5, h5N5, hM, h2M, hstride, N, M,
      size, dimension, modulus, pieceLength, pieces, chunks, descriptors, output,
      produced, heap, total, one, three, six, area, stride, temp, srcLeft, srcRight, addr,
      Fin.mk.injEq]
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · change M + M + 6 = 6 + 2 * M
      omega
    · change N + N + N + N + N + 5 = 5 + 5 * N
      omega
    · change N + N + N + N + 5 = 5 + 4 * N
      omega

private theorem pairBank_injective : Function.Injective pairBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 64 => k.val) h)

-- A specification of the delivered metadata, not a runtime layout input. Its scratch registers
-- are irrelevant: `InstancePair`'s arguments and record words read only registers17–28.
private def pairInput (x : Data 64) : Data 32 where
  regs i := match i.val with
    | 17 => x.regs srcLeft
    | 18 => x.regs srcRight
    | 19 => x.regs heap
    | 20 => x.regs size
    | 21 => x.regs dimension
    | 22 => x.regs modulus
    | 23 => (x.regs produced % x.regs pieces) * x.regs pieceLength
    | 24 => min (x.regs pieceLength)
        (x.regs size - (x.regs produced % x.regs pieces) * x.regs pieceLength)
    | 25 => x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors)
    | 26 => x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 1)
    | 27 => x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 2)
    | 28 => x.regs produced % x.regs pieces
    | _ => 0
  mem := x.mem

private def atInstance (x : Data 64) (i : ℕ) : Data 64 :=
  x.set produced i |>.set heap (x.regs output + i * x.regs stride)

private def Written (x : Data 64) (L R : ℕ → ℕ) (y : Data 64) (i : ℕ) : Prop :=
  let B := pairInput (atInstance x i)
  let M := x.regs size * x.regs dimension
  (Block.mk (x.regs output + i * x.regs stride) 6).Realizes y.mem (InstancePair.recordWords B) ∧
    (Block.mk (InstancePair.leftArgs B).dst M).Realizes y.mem
      (fun j => WriteMatrices.entry false (InstancePair.leftArgs B) L j) ∧
    (Block.mk (InstancePair.rightArgs B).dst M).Realizes y.mem
      (fun j => WriteMatrices.entry true (InstancePair.rightArgs B) R j)

private theorem pairInput_regs_congr (x y : Data 64)
    (hmeta : ∀ i : Fin 64, 32 ≤ i.val → i.val < 50 → y.regs i = x.regs i)
    (hH : 0 < x.regs pieces) (hi : x.regs produced < x.regs chunks * x.regs pieces)
    (hdir : x.regs descriptors + 3 * x.regs chunks ≤ x.regs output)
    (hmem : ∀ a < x.regs output, y.mem a = x.mem a) :
    (pairInput y).regs = (pairInput x).regs := by
  have hk : x.regs produced / x.regs pieces < x.regs chunks :=
    (Nat.div_lt_iff_lt_mul hH).mpr hi
  have hm0 := hmem (x.regs produced / x.regs pieces * 3 + x.regs descriptors) (by omega)
  have hm1 := hmem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 1) (by omega)
  have hm2 := hmem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 2) (by omega)
  funext i
  dsimp only [pairInput]
  rw [hmeta srcLeft (by decide) (by decide), hmeta srcRight (by decide) (by decide),
    hmeta heap (by decide) (by decide), hmeta size (by decide) (by decide),
    hmeta dimension (by decide) (by decide), hmeta modulus (by decide) (by decide),
    hmeta produced (by decide) (by decide), hmeta pieces (by decide) (by decide),
    hmeta pieceLength (by decide) (by decide), hmeta descriptors (by decide) (by decide),
    hm0, hm1, hm2]

private theorem exec_select {w : ℕ} (x : Data 64)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hH : 0 < x.regs pieces)
    (hi : x.regs produced < x.regs chunks * x.regs pieces)
    (hfit : Fits w (x.regs descriptors + 3 * x.regs chunks + x.regs size + x.regs pieces +
      x.regs pieces * x.regs pieceLength + 3)) :
    let k := x.regs produced / x.regs pieces
    let j := x.regs produced % x.regs pieces
    ∃ y, ExecWithin w select x y 14 ∧
      y.regs chunkIndex = k ∧ y.regs pieceIndex = j ∧
      y.regs rho = x.mem (k * 3 + x.regs descriptors) ∧
      y.regs queries = x.mem (k * 3 + x.regs descriptors + 1) ∧
      y.regs queryCount = x.mem (k * 3 + x.regs descriptors + 2) ∧
      y.regs first = j * x.regs pieceLength ∧
      y.regs length = min (x.regs pieceLength) (x.regs size - j * x.regs pieceLength) ∧
      y.mem = x.mem := by
  let k := x.regs produced / x.regs pieces
  let j := x.regs produced % x.regs pieces
  let f := j * x.regs pieceLength
  let a := k * 3 + x.regs descriptors
  let l := min (x.regs pieceLength) (x.regs size - f)
  have hk : k < x.regs chunks := (Nat.div_lt_iff_lt_mul hH).mpr hi
  have hj : j < x.regs pieces := Nat.mod_lt _ hH
  have hfirst : f ≤ x.regs pieces * x.regs pieceLength :=
    Nat.mul_le_mul_right _ hj.le
  have hkfit : Fits w k := hfit.of_le (by omega)
  have hjfit : Fits w j := hfit.of_le (by omega)
  have hk3 : Fits w (k * 3) := hfit.of_le (by omega)
  have ha : Fits w (k * 3 + x.regs descriptors) := hfit.of_le (by omega)
  have ha1 : Fits w (a + 1) := hfit.of_le (by dsimp [a]; omega)
  have ha2 : Fits w (a + 1 + 1) := hfit.of_le (by dsimp [a]; omega)
  have hf : Fits w f := hfit.of_le (by omega)
  have hsub : Fits w (x.regs size - f) := hfit.of_le (by omega)
  have hl : Fits w l := hsub.of_le (min_le_right ..)
  let y := x.set chunkIndex k |>.set pieceIndex j |>.set addr (k * 3)
    |>.set addr a |>.set rho (x.mem a) |>.set addr (a + 1)
    |>.set queries (x.mem (a + 1)) |>.set addr (a + 1 + 1)
    |>.set queryCount (x.mem (a + 1 + 1)) |>.set first f
    |>.set length (x.regs size - f) |>.set length l
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · by_cases h : x.regs pieceLength < x.regs size - f
    · have he : l = x.regs pieceLength := min_eq_left h.le
      rw [he] at hl
      ram_eval [select, y, k, j, f, a, l, he, h, ho, ht, hkfit, hjfit, hk3, ha,
        ha1, ha2, hf, hsub, hl, chunkIndex, produced, pieces, pieceIndex, addr, three,
        descriptors, rho, one, queries, queryCount, first, pieceLength, size, length,
        Fin.mk.injEq]
    · have he : l = x.regs size - f := min_eq_right (by omega)
      rw [he] at hl
      ram_eval [select, y, k, j, f, a, l, he, h, ho, ht, hkfit, hjfit, hk3, ha,
        ha1, ha2, hf, hsub, hl, chunkIndex, produced, pieces, pieceIndex, addr, three,
        descriptors, rho, one, queries, queryCount, first, pieceLength, size, length,
        Fin.mk.injEq]
  · simp +decide [y, k, chunkIndex, pieceIndex, addr, rho, queries, queryCount, first, length]
  · simp +decide [y, j, pieceIndex, addr, rho, queries, queryCount, first, length]
  · simp +decide [y, a, k, rho, addr, queries, queryCount, first, length]
  · simp +decide [y, a, k, queries, addr, queryCount, first, length]
  · simp +decide [y, a, k, queryCount, first, length, Nat.add_assoc]
  · simp +decide [y, f, j, first, length]
  · simp +decide [y, l, f, j, length]

private theorem exec_visit {w : ℕ} (x : Data 64) (L R : ℕ → ℕ)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hH : 0 < x.regs pieces)
    (hi : x.regs produced < x.regs chunks * x.regs pieces)
    (hstride : x.regs stride = 6 + 2 * (x.regs size * x.regs dimension))
    (hstart : (x.regs produced % x.regs pieces) * x.regs pieceLength ≤ x.regs size)
    (hrho : x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors) < x.regs modulus)
    (hL : ∀ i < x.regs size * x.regs size, L i < x.regs modulus)
    (hR : ∀ i < x.regs size * x.regs size, R i < x.regs modulus)
    (hleft : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcLeft + i) = L i)
    (hright : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcRight + i) = R i)
    (hsL : x.regs srcLeft + x.regs size * x.regs size ≤ x.regs heap)
    (hsR : x.regs srcRight + x.regs size * x.regs size ≤ x.regs heap)
    (hfit : Fits w (x.regs heap + x.regs stride + x.regs srcLeft + x.regs srcRight +
      2 * (x.regs size * x.regs size) + 2 * x.regs modulus + x.regs descriptors +
        3 * x.regs chunks + x.regs size + x.regs pieces +
          x.regs pieces * x.regs pieceLength + x.regs produced + 16)) :
    let B := pairInput x
    let M := x.regs size * x.regs dimension
    ∃ y, ExecWithin w visit x y (40 * M + 66) ∧
      y.regs produced = x.regs produced + 1 ∧ y.regs heap = x.regs heap + x.regs stride ∧
      (Block.mk (x.regs heap) 6).Realizes y.mem (InstancePair.recordWords B) ∧
      (Block.mk (InstancePair.leftArgs B).dst M).Realizes y.mem
        (fun i => WriteMatrices.entry false (InstancePair.leftArgs B) L i) ∧
      (Block.mk (InstancePair.rightArgs B).dst M).Realizes y.mem
        (fun i => WriteMatrices.entry true (InstancePair.rightArgs B) R i) ∧
      (∀ a, ¬(x.regs heap ≤ a ∧ a < x.regs heap + x.regs stride) → y.mem a = x.mem a) := by
  let B := pairInput x
  let M := x.regs size * x.regs dimension
  have Bbase : B.regs InstancePair.base = x.regs heap := rfl
  have Bn : B.regs InstancePair.size = x.regs size := rfl
  have BD : B.regs InstancePair.dimension = x.regs dimension := rfl
  have BsrcL : B.regs InstancePair.srcLeft = x.regs srcLeft := rfl
  have BsrcR : B.regs InstancePair.srcRight = x.regs srcRight := rfl
  have Bp : B.regs InstancePair.modulus = x.regs modulus := rfl
  obtain ⟨a, ha, hak, haj, harho, haq, hacount, hafirst, halen, hamem⟩ :=
    exec_select x ho ht hH hi (hfit.of_le (by omega))
  have hameta (i : Fin 64) (hi : i.val < 50) : a.regs i = x.regs i :=
    ha.regs_eq (select_preserves i hi)
  let b := a.set 17 (B.regs 17) |>.set 18 (B.regs 18) |>.set 19 (B.regs 19)
    |>.set 20 (B.regs 20) |>.set 21 (B.regs 21) |>.set 22 (B.regs 22)
    |>.set 23 (B.regs 23) |>.set 24 (B.regs 24) |>.set 25 (B.regs 25)
    |>.set 26 (B.regs 26) |>.set 27 (B.regs 27) |>.set 28 (B.regs 28)
  have hb : ExecWithin w deliver a b 12 := by
    have hsrcL := hameta srcLeft (by decide)
    have hsrcR := hameta srcRight (by decide)
    have hheap := hameta heap (by decide)
    have hn := hameta size (by decide)
    have hD := hameta dimension (by decide)
    have hp := hameta modulus (by decide)
    ram_eval [deliver, b, B, pairInput, hsrcL, hsrcR, hheap, hn, hD, hp, harho, haq,
      hacount, hafirst, halen, haj, srcLeft, srcRight, heap, size, dimension, modulus,
      first, length, rho, queries, queryCount, pieceIndex, Fin.mk.injEq]
  have bregs (i : Fin 32) (hi : 17 ≤ i.val) (hi' : i.val < 29) :
      (b.comap pairBank).regs i = B.regs i := by
    fin_cases i <;> simp +decide at hi hi' <;> simp +decide [b, pairBank]
  have hbLeft : InstancePair.leftArgs (b.comap pairBank) = InstancePair.leftArgs B := by
    unfold InstancePair.leftArgs
    rw [bregs InstancePair.srcLeft (by decide) (by decide),
      bregs InstancePair.base (by decide) (by decide),
      bregs InstancePair.size (by decide) (by decide),
      bregs InstancePair.dimension (by decide) (by decide),
      bregs InstancePair.modulus (by decide) (by decide),
      bregs InstancePair.first (by decide) (by decide),
      bregs InstancePair.length (by decide) (by decide),
      bregs InstancePair.rho (by decide) (by decide)]
  have hbRight : InstancePair.rightArgs (b.comap pairBank) = InstancePair.rightArgs B := by
    unfold InstancePair.rightArgs
    rw [hbLeft, bregs InstancePair.srcRight (by decide) (by decide),
      bregs InstancePair.base (by decide) (by decide),
      bregs InstancePair.size (by decide) (by decide),
      bregs InstancePair.dimension (by decide) (by decide)]
  have hbRecord : InstancePair.recordWords (b.comap pairBank) = InstancePair.recordWords B := by
    unfold InstancePair.recordWords
    rw [hbLeft, hbRight, bregs InstancePair.rho (by decide) (by decide),
      bregs InstancePair.piece (by decide) (by decide),
      bregs InstancePair.queries (by decide) (by decide),
      bregs InstancePair.count (by decide) (by decide)]
  have hRho : (b.comap pairBank).regs InstancePair.rho <
      (b.comap pairBank).regs InstancePair.modulus := by
    rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide)]
    exact hrho
  have hPiece : (b.comap pairBank).regs InstancePair.first +
      (b.comap pairBank).regs InstancePair.length ≤ (b.comap pairBank).regs InstancePair.size := by
    rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide),
      bregs _ (by decide) (by decide)]
    change (x.regs produced % x.regs pieces) * x.regs pieceLength +
      min (x.regs pieceLength)
        (x.regs size - (x.regs produced % x.regs pieces) * x.regs pieceLength) ≤ x.regs size
    have := min_le_right (x.regs pieceLength)
      (x.regs size - (x.regs produced % x.regs pieces) * x.regs pieceLength)
    omega
  obtain ⟨v, hv, hrecord, hmatL, hmatR, hframe⟩ := InstancePair.exec (b.comap pairBank) L R
    hRho hPiece
    (by
      rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide)]
      exact hL)
    (by
      rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide)]
      exact hR)
    (by
      intro i hi
      rw [bregs _ (by decide) (by decide)]
      change a.mem (x.regs srcLeft + i) = L i
      rw [hamem]
      exact hleft i hi)
    (by
      intro i hi
      rw [bregs _ (by decide) (by decide)]
      change a.mem (x.regs srcRight + i) = R i
      rw [hamem]
      exact hright i hi)
    (by
      rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide),
        bregs _ (by decide) (by decide)]
      exact hsL)
    (by
      rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide),
        bregs _ (by decide) (by decide)]
      exact hsR)
    (hfit.of_le (by
      rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide),
        bregs _ (by decide) (by decide), bregs _ (by decide) (by decide),
        bregs _ (by decide) (by decide), bregs _ (by decide) (by decide)]
      rw [Bbase, Bn, BD, BsrcL, BsrcR, Bp, hstride]
      omega))
  rw [bregs InstancePair.size (by decide) (by decide), Bn,
    bregs InstancePair.dimension (by decide) (by decide), BD] at hv
  rw [hbRecord, bregs InstancePair.base (by decide) (by decide), Bbase] at hrecord
  rw [hbLeft, bregs InstancePair.size (by decide) (by decide), Bn,
    bregs InstancePair.dimension (by decide) (by decide), BD] at hmatL
  rw [hbRight, bregs InstancePair.size (by decide) (by decide), Bn,
    bregs InstancePair.dimension (by decide) (by decide), BD] at hmatR
  let c := v.extend pairBank b
  have hc : ExecWithin w pair b c (40 * M + 38) := by
    simpa only [pair, c, M] using hv.rename pairBank_injective
  have hprefix (i : Fin 64) (hi : 32 ≤ i.val) (hi' : i.val < 50) :
      c.regs i = x.regs i := (ha.seq (hb.seq hc)).regs_eq (prefix_preserves i hi hi')
  let y := c.set heap (x.regs heap + x.regs stride) |>.set produced (x.regs produced + 1)
  have hheapFit : Fits w (x.regs heap + x.regs stride) := hfit.of_le (by omega)
  have hcountFit : Fits w (x.regs produced + 1) := hfit.of_le (by omega)
  have hadvance : ExecWithin w advance c y 2 := by
    have hh := hprefix heap (by decide) (by decide)
    have hs := hprefix stride (by decide) (by decide)
    have hp := hprefix produced (by decide) (by decide)
    have h1 := hprefix one (by decide) (by decide)
    ram_eval [advance, y, hh, hs, hp, h1, ho, hheapFit, hcountFit, heap, stride, produced,
      one, Fin.mk.injEq]
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert ha.seq (hb.seq (hc.seq hadvance)) using 1 <;>
      first | rfl | (dsimp [M]; ring)
  · simp [y]
  · simp +decide [y, heap, produced]
  · exact hrecord
  · exact hmatL
  · exact hmatR
  · intro j hj
    change v.mem j = x.mem j
    rw [hframe j ?_]
    · exact congrFun hamem j
    · rw [bregs _ (by decide) (by decide), bregs _ (by decide) (by decide),
        bregs _ (by decide) (by decide)]
      change ¬(x.regs heap ≤ j ∧ j < x.regs heap + 6 + 2 * (x.regs size * x.regs dimension))
      rw [hstride] at hj
      omega

private theorem exec_loop {w : ℕ} (x : Data 64) (L R : ℕ → ℕ)
    (hzero : x.regs produced = 0) (hheap : x.regs heap = x.regs output)
    (htotal : x.regs total = x.regs chunks * x.regs pieces)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hH : 0 < x.regs pieces)
    (hstride : x.regs stride = 6 + 2 * (x.regs size * x.regs dimension))
    (hstart : ∀ j < x.regs pieces, j * x.regs pieceLength ≤ x.regs size)
    (hdir : x.regs descriptors + 3 * x.regs chunks ≤ x.regs output)
    (hrho : ∀ k < x.regs chunks, x.mem (k * 3 + x.regs descriptors) < x.regs modulus)
    (hL : ∀ i < x.regs size * x.regs size, L i < x.regs modulus)
    (hR : ∀ i < x.regs size * x.regs size, R i < x.regs modulus)
    (hleft : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcLeft + i) = L i)
    (hright : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcRight + i) = R i)
    (hsL : x.regs srcLeft + x.regs size * x.regs size ≤ x.regs output)
    (hsR : x.regs srcRight + x.regs size * x.regs size ≤ x.regs output)
    (hfit : Fits w (x.regs output + x.regs total * x.regs stride + x.regs srcLeft +
      x.regs srcRight + 2 * (x.regs size * x.regs size) + 2 * x.regs modulus +
        x.regs descriptors + 3 * x.regs chunks + x.regs size + x.regs pieces +
          x.regs pieces * x.regs pieceLength + x.regs total + 16)) :
    ∃ y, ExecWithin w (.loop (.lt produced total) visit) x y
        (x.regs total * (40 * (x.regs size * x.regs dimension) + 68) + 2) ∧
      y.regs produced = x.regs total ∧
      y.regs heap = x.regs output + x.regs total * x.regs stride ∧
      (∀ i < x.regs total, Written x L R y i) ∧
      (∀ a, ¬(x.regs output ≤ a ∧ a < y.regs heap) → y.mem a = x.mem a) := by
  let M := x.regs size * x.regs dimension
  let T := x.regs total
  let I (y : Data 64) : Prop :=
    (∀ i : Fin 64, 32 ≤ i.val → i.val < 50 → i ≠ produced → i ≠ heap →
      y.regs i = x.regs i) ∧
      y.regs produced ≤ T ∧
      y.regs heap = x.regs output + y.regs produced * x.regs stride ∧
      (∀ j < y.regs produced, Written x L R y j) ∧
      (∀ a, ¬(x.regs output ≤ a ∧ a < y.regs heap) → y.mem a = x.mem a)
  have hbody (y : Data 64) (hy : I y) (hc : (Cond.lt produced total).Holds y) :
      ∃ z, ExecWithin w visit y z (40 * M + 66) ∧ I z ∧
        T - z.regs produced < T - y.regs produced := by
    obtain ⟨hyr, hyi, hyheap, hywritten, hyframe⟩ := hy
    have hreg (i : Fin 64)
        (hi : 32 ≤ i.val ∧ i.val < 50 ∧ i ≠ produced ∧ i ≠ heap) :
        y.regs i = x.regs i := hyr i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hyT := hreg total (by decide)
    have hyN := hreg size (by decide)
    have hyD := hreg dimension (by decide)
    have hyp := hreg modulus (by decide)
    have hyH := hreg pieces (by decide)
    have hyB := hreg pieceLength (by decide)
    have hyK := hreg chunks (by decide)
    have hyd := hreg descriptors (by decide)
    have hys := hreg stride (by decide)
    have hyL := hreg srcLeft (by decide)
    have hyR := hreg srcRight (by decide)
    have hyo := hreg one (by decide)
    have hyt := hreg three (by decide)
    have hlt : y.regs produced < T := by simpa only [Cond.holds_lt, hyT] using hc
    have hi : y.regs produced < x.regs chunks * x.regs pieces := by
      simpa only [T, htotal] using hlt
    have hk : y.regs produced / x.regs pieces < x.regs chunks :=
      (Nat.div_lt_iff_lt_mul hH).mpr hi
    have hstep : y.regs produced * x.regs stride + x.regs stride ≤ T * x.regs stride := by
      have h := Nat.mul_le_mul_right (x.regs stride) (Nat.succ_le_of_lt hlt)
      simpa only [Nat.succ_mul] using h
    have hreadonly (a : ℕ) (ha : a < x.regs output) : y.mem a = x.mem a :=
      hyframe a (by omega)
    obtain ⟨z, hz, hzi, hzh, hzrecord, hzL, hzR, hzframe⟩ := exec_visit y L R
      (hyo.trans ho) (hyt.trans ht) (by simpa only [hyH] using hH)
      (by simpa only [hyK, hyH] using hi)
      (by simpa only [hys, hyN, hyD] using hstride)
      (by rw [hyH, hyB, hyN]; exact hstart _ (Nat.mod_lt _ hH))
      (by rw [hyH, hyd, hyp, hreadonly _ (by omega)]; exact hrho _ hk)
      (by simpa only [hyN, hyp] using hL)
      (by simpa only [hyN, hyp] using hR)
      (by
        intro i hi
        rw [hyN] at hi
        rw [hyL, hreadonly _ (by omega)]
        exact hleft i hi)
      (by
        intro i hi
        rw [hyN] at hi
        rw [hyR, hreadonly _ (by omega)]
        exact hright i hi)
      (by rw [hyL, hyN, hyheap]; omega)
      (by rw [hyR, hyN, hyheap]; omega)
      (hfit.of_le (by
        rw [hyheap, hys, hyL, hyR, hyN, hyp, hyd, hyK, hyH, hyB]
        dsimp only [T] at hstep hyi
        omega))
    rw [hyN, hyD] at hz
    rw [hys] at hzh hzframe
    let old := atInstance x (y.regs produced)
    have hmeta : ∀ i : Fin 64, 32 ≤ i.val → i.val < 50 → y.regs i = old.regs i := by
      intro i hi hi'
      by_cases hp : i = produced
      · subst i
        simp +decide [old, atInstance, produced, heap]
      · by_cases hh : i = heap
        · subst i
          simpa +decide [old, atInstance, produced, heap] using hyheap
        · simpa only [old, atInstance, Data.set_regs, Function.update_of_ne hh,
            Function.update_of_ne hp] using hyr i hi hi' hp hh
    have hinputRegs : (pairInput y).regs = (pairInput old).regs :=
      pairInput_regs_congr old y hmeta
        (by simpa +decide [old, atInstance, pieces, heap, produced] using hH)
        (by simpa +decide [old, atInstance, chunks, pieces, heap, produced] using hi)
        (by simpa +decide [old, atInstance, descriptors, chunks, output, heap, produced] using hdir)
        (by simpa +decide [old, atInstance, output, heap, produced] using hreadonly)
    have hargsL : InstancePair.leftArgs (pairInput y) = InstancePair.leftArgs (pairInput old) := by
      unfold InstancePair.leftArgs
      rw [hinputRegs]
    have hargsR : InstancePair.rightArgs (pairInput y) =
        InstancePair.rightArgs (pairInput old) := by
      unfold InstancePair.rightArgs InstancePair.leftArgs
      rw [hinputRegs]
    have hrecord : InstancePair.recordWords (pairInput y) =
        InstancePair.recordWords (pairInput old) := by
      unfold InstancePair.recordWords InstancePair.leftArgs InstancePair.rightArgs
      rw [hinputRegs]
    rw [hrecord, hyheap] at hzrecord
    rw [hargsL, hyN, hyD] at hzL
    rw [hargsR, hyN, hyD] at hzR
    have hpres (i : Fin 64)
        (hi : 32 ≤ i.val ∧ i.val < 50 ∧ i ≠ heap ∧ i ≠ produced) :
        z.regs i = y.regs i := hz.regs_eq (visit_preserves i hi)
    have hnew : Written x L R z (y.regs produced) := ⟨hzrecord, hzL, hzR⟩
    have hzreadonly (a : ℕ) (ha : a < y.regs heap) : z.mem a = y.mem a :=
      hzframe a (by omega)
    refine ⟨z, hz, ⟨?_, by omega, ?_, ?_, ?_⟩, by omega⟩
    · intro i hi hi' hp hh
      exact (hpres i ⟨hi, hi', hh, hp⟩).trans (hyr i hi hi' hp hh)
    · rw [hzh, hyheap, hzi, Nat.add_mul, Nat.one_mul]
      omega
    · intro j hj
      rw [hzi] at hj
      by_cases hji : j = y.regs produced
      · simpa only [hji] using hnew
      · have hjlt : j < y.regs produced := by omega
        obtain ⟨hjrecord, hjL, hjR⟩ := hywritten j hjlt
        have hprev : j * x.regs stride + x.regs stride ≤ y.regs produced * x.regs stride := by
          have h := Nat.mul_le_mul_right (x.regs stride) (Nat.succ_le_of_lt hjlt)
          simpa only [Nat.succ_mul] using h
        refine ⟨?_, ?_, ?_⟩
        · intro a
          change z.mem (x.regs output + j * x.regs stride + a.val) = _
          rw [hzreadonly _ (by
            have ha : a.val < 6 := a.isLt
            rw [hyheap]
            omega)]
          exact hjrecord a
        · intro a
          change z.mem ((InstancePair.leftArgs (pairInput (atInstance x j))).dst + a.val) = _
          rw [hzreadonly _ (by
            have ha : a.val < M := a.isLt
            change x.regs output + j * x.regs stride + 6 + a.val < y.regs heap
            rw [hyheap]
            dsimp [M] at ha
            omega)]
          exact hjL a
        · intro a
          change z.mem ((InstancePair.rightArgs (pairInput (atInstance x j))).dst + a.val) = _
          rw [hzreadonly _ (by
            have ha : a.val < M := a.isLt
            change x.regs output + j * x.regs stride + 6 + M + a.val < y.regs heap
            rw [hyheap]
            dsimp [M] at ha ⊢
            omega)]
          exact hjR a
    · intro a ha
      rw [hzh] at ha
      rw [hzframe a (by omega), hyframe a (by omega)]
  have hx : I x := by
    refine ⟨fun _ _ _ _ _ => rfl, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [hzero]
      exact Nat.zero_le _
    · rw [hzero, Nat.zero_mul, Nat.add_zero]
      exact hheap
    · intro j hj
      rw [hzero] at hj
      omega
  obtain ⟨y, hy, hI, hend⟩ := ExecWithin.loop_invariant I (fun y => T - y.regs produced) hbody hx
  obtain ⟨hmeta, hcount, hheap', hwritten, hframe⟩ := hI
  have hyT : y.regs total = T := hmeta total (by decide) (by decide) (by decide) (by decide)
  have hfinal : y.regs produced = T := by
    simp only [Cond.holds_lt, hyT] at hend
    omega
  refine ⟨y, ?_, hfinal, ?_, ?_, hframe⟩
  · simpa only [hzero, Nat.sub_zero] using hy
  · simpa only [hfinal] using hheap'
  · simpa only [hfinal] using hwritten

private theorem written_readback {n D p B H K desc out i : ℕ}
    (b y : Data 64) (L R : ℕ → ℕ) (hH : 0 < H) (hi : i < K * H)
    (hmeta : b.regs size = n ∧ b.regs dimension = D ∧ b.regs modulus = p ∧
      b.regs pieceLength = B ∧ b.regs pieces = H ∧ b.regs descriptors = desc ∧
      b.regs output = out ∧ b.regs stride = 6 + 2 * (n * D) ∧
      b.regs srcLeft = 5 + 5 * (n * n) ∧ b.regs srcRight = 5 + 4 * (n * n))
    (hdirBound : desc + 3 * K ≤ out)
    (hframe : ∀ q < out, y.mem q = b.mem q) (hwritten : Written b L R y i) :
    let base := out + i * (6 + 2 * (n * D))
    let A : WriteMatrices.Args :=
      ⟨5 + 5 * (n * n), base + 6, n, D, p, i % H * B, min B (n - i % H * B),
        y.mem (desc + 3 * (i / H))⟩
    let A' := { A with src := 5 + 4 * (n * n), dst := base + 6 + n * D }
    (Block.mk base 6).Realizes y.mem
      ![A.rho, i % H, y.mem (desc + 3 * (i / H) + 1),
        y.mem (desc + 3 * (i / H) + 2), base + 6, base + 6 + n * D] ∧
      (Block.mk A.dst (n * D)).Realizes y.mem (fun j => WriteMatrices.entry false A L j) ∧
      (Block.mk A'.dst (n * D)).Realizes y.mem (fun j => WriteMatrices.entry true A' R j) := by
  obtain ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩ := hmeta
  let N := n * n
  let S := 6 + 2 * (n * D)
  let base := out + i * S
  let A : WriteMatrices.Args :=
    ⟨5 + 5 * N, base + 6, n, D, p, i % H * B, min B (n - i % H * B),
      y.mem (desc + 3 * (i / H))⟩
  let A' := { A with src := 5 + 4 * N, dst := base + 6 + n * D }
  have hk : i / H < K := (Nat.div_lt_iff_lt_mul hH).mpr hi
  have hdir (t : ℕ) (ht : t < 3) :
      b.mem (i / H * 3 + desc + t) = y.mem (desc + 3 * (i / H) + t) := by
    have heq : i / H * 3 + desc + t = desc + 3 * (i / H) + t := by omega
    rw [heq]
    exact (hframe _ (by omega)).symm
  have hd0 : b.mem (i / H * 3 + desc) = y.mem (desc + 3 * (i / H)) := by
    simpa only [Nat.add_zero] using hdir 0 (by decide)
  have hd1 := hdir 1 (by decide)
  have hd2 := hdir 2 (by decide)
  have hargsL : InstancePair.leftArgs (pairInput (atInstance b i)) = A := by
    simp +decide [InstancePair.leftArgs, pairInput, atInstance, A, base, N, S,
      hbn, hbD, hbp, hbH, hbB, hbL, hbo, hbs, hbd, hd0,
      InstancePair.srcLeft, InstancePair.base, InstancePair.size, InstancePair.dimension,
      InstancePair.modulus, InstancePair.first, InstancePair.length, InstancePair.rho,
      produced, heap]
  have hargsR : InstancePair.rightArgs (pairInput (atInstance b i)) = A' := by
    unfold InstancePair.rightArgs
    rw [hargsL]
    simp +decide [pairInput, atInstance, A', A, base, N, S,
      hbn, hbD, hbR, hbo, hbs, InstancePair.srcRight, InstancePair.base,
      InstancePair.size, InstancePair.dimension, produced, heap]
  have hwords : InstancePair.recordWords (pairInput (atInstance b i)) =
      ![A.rho, i % H, y.mem (desc + 3 * (i / H) + 1),
        y.mem (desc + 3 * (i / H) + 2), base + 6, base + 6 + n * D] := by
    rw [InstancePair.recordWords, hargsL, hargsR]
    simp +decide [pairInput, atInstance, A, A', base, hbH, hbd, hd0, hd1, hd2,
      InstancePair.rho, InstancePair.piece, InstancePair.queries, InstancePair.count,
      produced, heap]
  obtain ⟨hr, hL, hR⟩ := hwritten
  dsimp only at hr hL hR
  rw [hbo, hbs, hwords] at hr
  rw [hargsL, hbn, hbD] at hL
  rw [hargsR, hbn, hbD] at hR
  refine ⟨?_, ?_, ?_⟩
  · exact hr
  · exact hL
  · exact hR

/-- Exact computed catalogue, record and raw zero/one matrix readback, with the complete
input/output frame. The matrix predicates reuse the existing writer arguments and entry
semantics. -/
@[expose]
def Output (n D g p : ℕ) (values : ℕ → ℤ) (initial y : Data 64) : Prop :=
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let K := ChunkCatalogue.before C (queryCap n D) p
    let H := numPieces n D g
    let B := pieceSize D g
    let desc := 5 + 6 * N + p + 2 * N * p
    let out := desc + 3 * K
    y.regs size = n ∧ y.regs dimension = D ∧ y.regs modulus = p ∧
    y.regs output = out ∧ y.regs produced = K * H ∧
    y.regs heap = out + (K * H) * (6 + 2 * (n * D)) ∧
    (∀ q < 3 * N, y.mem (5 + 3 * N + q) = R q) ∧
    (∀ rho < p, y.mem (5 + 6 * N + rho) = C rho) ∧
    (∀ rho < p, ∀ q < N, R q = rho →
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q) = q / n ∧
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1) = q % n) ∧
    (∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
      y.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
      y.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
        5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
      y.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
        min (queryCap n D) (C rho - k * queryCap n D)) ∧
    (∀ i < K * H,
      let base := out + i * (6 + 2 * (n * D))
      let residue := y.mem (desc + 3 * (i / H))
      let A : WriteMatrices.Args :=
        ⟨5 + 5 * N, base + 6, n, D, p, i % H * B, min B (n - i % H * B), residue⟩
      let A' := { A with src := 5 + 4 * N, dst := base + 6 + n * D }
      (Block.mk base 6).Realizes y.mem
        ![residue, i % H, y.mem (desc + 3 * (i / H) + 1),
          y.mem (desc + 3 * (i / H) + 2), base + 6, base + 6 + n * D] ∧
        (Block.mk A.dst (n * D)).Realizes y.mem
          (fun j => WriteMatrices.entry false A (fun q => R (2 * N + q)) j) ∧
        (Block.mk A'.dst (n * D)).Realizes y.mem
          (fun j => WriteMatrices.entry true A' (fun q => R (N + q)) j)) ∧
    (∀ a, a < 5 + 3 * N ∨ out + (K * H) * (6 + 2 * (n * D)) ≤ a →
      y.mem a = initial.mem a)

private theorem output_of_loop {n D g p : ℕ} (values : ℕ → ℤ)
    (initial : Data 64) (v : Data 32) (b y : Data 64)
    (hcat : Catalogue.Output n D g p values (initial.comap pairBank) v)
    (hbmem : b.mem = v.mem)
    (hmeta :
      let N := n * n
      let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) N
      let K := ChunkCatalogue.before C (queryCap n D) p
      let H := numPieces n D g
      let B := pieceSize D g
      let desc := 5 + 6 * N + p + 2 * N * p
      let out := desc + 3 * K
      b.regs size = n ∧ b.regs dimension = D ∧ b.regs modulus = p ∧
        b.regs pieceLength = B ∧ b.regs pieces = H ∧ b.regs descriptors = desc ∧
        b.regs output = out ∧ b.regs stride = 6 + 2 * (n * D) ∧
        b.regs srcLeft = 5 + 5 * N ∧ b.regs srcRight = 5 + 4 * N)
    (hY : y.regs size = n ∧ y.regs dimension = D ∧ y.regs modulus = p ∧
      y.regs output = b.regs output)
    (hycount : y.regs produced =
      ChunkCatalogue.before (fun rho => Nat.count
        (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)) (queryCap n D) p * numPieces n D g)
    (hyheap : y.regs heap = b.regs output + y.regs produced * b.regs stride)
    (hH : 0 < numPieces n D g)
    (hywritten : ∀ i < y.regs produced,
      Written b (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat)
        (fun q => (values (n * n + q) % (p : ℤ)).toNat) y i)
    (hyframe : ∀ q, ¬(b.regs output ≤ q ∧ q < y.regs heap) → y.mem q = b.mem q) :
    Output n D g p values initial y := by
  let N := n * n
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let B := pieceSize D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  let S := 6 + 2 * (n * D)
  obtain ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩ := hmeta
  obtain ⟨hyn, hyD, hyp, hyo⟩ := hY
  change b.regs pieceLength = B at hbB
  change b.regs pieces = H at hbH
  change b.regs descriptors = desc at hbd
  change b.regs output = out at hbo
  change b.regs srcLeft = 5 + 5 * N at hbL
  change b.regs srcRight = 5 + 4 * N at hbR
  obtain ⟨-, -, -, -, -, -, -, -, hvK, -, hvres, hvcounts, hvpairs, hvdesc, hvframe⟩ := hcat
  change v.regs ChunkCatalogue.written = K at hvK
  change ∀ q, q < 5 + 3 * N ∨ desc + 3 * v.regs ChunkCatalogue.written ≤ q →
    v.mem q = initial.mem q at hvframe
  change ∀ q < 3 * N, v.mem (5 + 3 * N + q) = R q at hvres
  change ∀ rho < p, v.mem (5 + 6 * N + rho) = C rho at hvcounts
  change ∀ rho < p, ∀ q < N, R q = rho →
    v.mem (5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q) = q / n ∧
    v.mem (5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q + 1) = q % n
    at hvpairs
  change ∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
      5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
      min (queryCap n D) (C rho - k * queryCap n D) at hvdesc
  change y.regs produced = K * H at hycount
  rw [hbo, hycount, hbs] at hyheap
  rw [hycount] at hywritten
  have hbefore (q : ℕ) (hq : q < out) : y.mem q = v.mem q :=
    (hyframe q (by rw [hbo]; omega)).trans (congrFun hbmem q)
  refine ⟨hyn, hyD, hyp, hyo.trans hbo, hycount, hyheap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [hbefore _ (by dsimp [out, desc]; omega)]
    exact hvres q hq
  · intro rho hrho
    rw [hbefore _ (by dsimp [out, desc]; omega)]
    exact hvcounts rho hrho
  · intro rho hrho q hq hRq
    change q < N at hq
    change R q = rho at hRq
    have hcount : Nat.count (fun k => R k = rho) q ≤ q := Nat.count_le _
    have hbound := Nat.mul_le_mul_left (2 * N) (Nat.succ_le_of_lt hrho)
    rw [Nat.mul_succ] at hbound
    have h0 : 5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q < out := by
      dsimp only [out, desc]
      omega
    have h1 : 5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1 < out := by
      dsimp only [out, desc]
      omega
    have hread := hvpairs rho hrho q hq hRq
    exact ⟨(hbefore _ h0).trans hread.1, (hbefore _ h1).trans hread.2⟩
  · intro rho hrho k hk
    change k < C rho ⌈/⌉ queryCap n D at hk
    have hindex : ChunkCatalogue.before C (queryCap n D) rho + k < K :=
      ChunkCatalogue.before_add_lt C (queryCap n D) hrho hk
    have h0 : desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) < out := by
      dsimp only [out]
      omega
    have h1 : desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1 < out := by
      dsimp only [out]
      omega
    have h2 : desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2 < out := by
      dsimp only [out]
      omega
    have hread := hvdesc rho hrho k hk
    exact ⟨(hbefore _ h0).trans hread.1, (hbefore _ h1).trans hread.2.1,
      (hbefore _ h2).trans hread.2.2⟩
  · intro i hi
    exact written_readback (n := n) (D := D) (p := p) (B := B) (H := H) (K := K)
      (desc := desc) (out := out) (i := i)
      b y (fun q => R (2 * N + q)) (fun q => R (N + q)) hH hi
      ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩
      (by dsimp only [out]; omega)
      (fun q hq => hyframe q (by rw [hbo]; omega)) (hywritten i hi)
  · intro q hq
    change q < 5 + 3 * N ∨ out + K * H * S ≤ q at hq
    rw [hyframe q (by
      rw [hbo, hyheap]
      change ¬(out ≤ q ∧ q < out + K * H * S)
      rcases hq with h | h
      · have : 5 + 3 * N ≤ out := by dsimp only [out, desc]; omega
        omega
      · omega), hbmem]
    apply hvframe q
    rcases hq with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hvK]; omega)

/-- Execute the complete preparation from the real header and signed matrices. Every output
record refers to the actual computed query chunk, followed by its raw zero/one matrix pair.
The only resource premises concern the original signed values and the explicit numeric budget;
neither a catalogue nor a layout or execution certificate is an input. The final halt is
excluded here and added by the initialized flat-program client. -/
theorem exec_at {w : ℕ} (n D g p : ℕ) (values : ℕ → ℤ) (initial : Data 64)
    (hDHeader : initial.mem 1 = D) (hgHeader : initial.mem 2 = g)
    (hnHeader : initial.mem 3 = n) (hpHeader : initial.mem 4 = p)
    (hinput : ∀ q < 3 * (n * n), initial.mem (5 + q) = Signed.encode (values q))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (hbudget : Fits (w + 2) (budget n D g p)) :
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let K := ChunkCatalogue.before C (queryCap n D) p
    let H := numPieces n D g
    ∃ y, ExecWithin (w + 2) program initial y (timeBound n D p K H - 1) ∧
      Output n D g p values initial y := by
  let N := n * n
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  let C (rho : ℕ) := Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let B := pieceSize D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  let S := 6 + 2 * (n * D)
  obtain ⟨-, hBn, hH, hHn, hstart⟩ := parameter_bounds hD hDn hg
  change B ≤ n at hBn
  change 0 < H at hH
  change H ≤ n at hHn
  change ∀ j < H, j * B ≤ n at hstart
  have hK : K ≤ p * N := ChunkCatalogue.before_le (one_le_queryCap hD hDn)
    (fun _ _ => Nat.count_le _) le_rfl
  have hHB : H * B ≤ N := Nat.mul_le_mul hHn hBn
  have hCatalogue : Catalogue.budget n D g p ≤ budget n D g p := by
    dsimp only [budget]
    omega
  obtain ⟨v, hv, hcatOriginal⟩ := Catalogue.exec_at n D g p values
    (initial.comap pairBank) hDHeader hgHeader hnHeader hpHeader hinput hD hDn hg hp
    hmod hvalues (hbudget.of_le hCatalogue)
  have hcatSave := hcatOriginal
  obtain ⟨hvn, hvp, -, -, hvd, -, hvB, hvH, hvK, hvheap,
    hvres, hvcounts, hvpairs, hvdesc, hvframe⟩ := hcatOriginal
  change v.regs ChunkCatalogue.written = K at hvK
  change v.regs ChunkCatalogue.heap = desc + 3 * v.regs ChunkCatalogue.written at hvheap
  change ∀ q < 3 * N, v.mem (5 + 3 * N + q) = R q at hvres
  change ∀ rho < p, v.mem (5 + 6 * N + rho) = C rho at hvcounts
  change ∀ rho < p, ∀ q < N, R q = rho →
    v.mem (5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q) = q / n ∧
    v.mem (5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q + 1) = q % n
    at hvpairs
  change ∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
      5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
      min (queryCap n D) (C rho - k * queryCap n D) at hvdesc
  let a := v.extend pairBank initial
  have ha : ExecWithin (w + 2) catalogue initial a (Catalogue.cost n D p) :=
    hv.rename pairBank_injective
  have haLow (i : Fin 32) : a.regs (pairBank i) = v.regs i :=
    pairBank_injective.extend_apply _ _ i
  have ha16 : a.regs 16 = n := (haLow ChunkCatalogue.size).trans hvn
  have ha17 : a.regs 17 = p := (haLow ChunkCatalogue.modulus).trans hvp
  have ha28 : a.regs 28 = B := (haLow Catalogue.pieceLength).trans hvB
  have ha29 : a.regs 29 = H := (haLow Catalogue.pieces).trans hvH
  have ha21 : a.regs 21 = K := (haLow ChunkCatalogue.written).trans hvK
  have ha18 : a.regs 18 = desc := (haLow ChunkCatalogue.dst).trans hvd
  have ha22 : a.regs 22 = out := by
    change a.regs (pairBank ChunkCatalogue.heap) = out
    rw [haLow ChunkCatalogue.heap, hvheap, hvK]
  have haD : a.mem 1 = D := (hvframe 1 (Or.inl (by omega))).trans hDHeader
  obtain ⟨b, hb, hbmem, hbn, hbD, hbp, hbB, hbH, hbK, hbd, hbo, hbzero, hbt,
      hbh, hbs, hb1, hb3, hbL, hbR⟩ := exec_setup a n D p B H K desc out
    ha16 ha17 ha28 ha29 ha21 ha18 ha22 haD (hbudget.of_le (budget_covers_setup hK hHn))
  change b.regs srcLeft = 5 + 5 * N at hbL
  change b.regs srcRight = 5 + 4 * N at hbR
  have hres (q : ℕ) : R q < p := Int.natMod_lt (by omega)
  have hleft (i : ℕ) (hi : i < N) : b.mem (5 + 5 * N + i) = R (2 * N + i) := by
    rw [hbmem]
    change v.mem (5 + 5 * N + i) = R (2 * N + i)
    convert hvres (2 * N + i) (by omega) using 1
    congr 1
    omega
  have hright (i : ℕ) (hi : i < N) : b.mem (5 + 4 * N + i) = R (N + i) := by
    rw [hbmem]
    change v.mem (5 + 4 * N + i) = R (N + i)
    convert hvres (N + i) (by omega) using 1
    congr 1
    omega
  obtain ⟨y, hy, hycount, hyheap, hywritten, hyframe⟩ := exec_loop b
    (fun q => R (2 * N + q)) (fun q => R (N + q)) hbzero (hbh.trans hbo.symm)
    (by rw [hbt, hbK, hbH]) hb1 hb3 (by rw [hbH]; exact hH)
    (by rw [hbs, hbn, hbD])
    (by rw [hbH, hbB, hbn]; exact hstart)
    (by rw [hbd, hbK, hbo])
    (by
      rw [hbK, hbd, hbp]
      intro k hk
      obtain ⟨idx, hidx, -⟩ := ChunkCatalogue.before_index C (queryCap n D) p k hk
      rw [hbmem]
      have hr := (hvdesc idx.1.val idx.1.isLt idx.2.val idx.2.isLt).1
      have heq : v.mem (k * 3 + desc) = idx.1.val := by
        simpa only [hidx, Nat.mul_comm, Nat.add_comm] using hr
      exact heq ▸ idx.1.isLt)
    (by rw [hbn, hbp]; exact fun q _ => hres (2 * N + q))
    (by rw [hbn, hbp]; exact fun q _ => hres (N + q))
    (by rw [hbL, hbn]; exact hleft)
    (by rw [hbR, hbn]; exact hright)
    (by rw [hbL, hbn, hbo]; dsimp [out, desc, N]; omega)
    (by rw [hbR, hbn, hbo]; dsimp [out, desc, N]; omega)
    (hbudget.of_le (by
      rw [hbo, hbt, hbs, hbL, hbR, hbn, hbp, hbd, hbK, hbH, hbB]
      change out + K * H * S + (5 + 5 * N) + (5 + 4 * N) + 2 * N + 2 * p +
        desc + 3 * K + n + H + H * B + K * H + 16 ≤ _
      calc
        _ = 2 * out + K * H * S + 11 * N + 2 * p + n + H + H * B + K * H + 26 := by
          dsimp only [out]
          ring
        _ ≤ _ := budget_covers_loop hK hHn hHB))
  rw [hbn, hbD, hbt] at hy
  rw [hbt] at hycount hywritten
  rw [hbo, hbt, hbs] at hyheap
  have hyreg (i : Fin 64) (hi : 32 ≤ i.val ∧ i.val < 50 ∧ i ≠ heap ∧ i ≠ produced) :
      y.regs i = b.regs i := hy.regs_eq (visit_preserves i hi)
  refine ⟨y, ?_, ?_⟩
  · apply (ha.seq (hb.seq hy)).mono
    change Catalogue.cost n D p + (26 + (K * H * (40 * (n * D) + 68) + 2)) ≤
      Catalogue.cost n D p + K * H * (40 * (n * D) + 68) + 29 - 1
    omega
  · apply output_of_loop values initial v b y hcatSave hbmem
      ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩
      ⟨(hyreg size (by decide)).trans hbn, (hyreg dimension (by decide)).trans hbD,
        (hyreg modulus (by decide)).trans hbp, hyreg output (by decide)⟩ hycount
      (by rw [hbo, hycount, hbs]; exact hyheap) hH
      (by rw [hycount]; exact hywritten) hyframe

end Cslib.Algorithms.WordRAM.ExactTriangle.Instances
