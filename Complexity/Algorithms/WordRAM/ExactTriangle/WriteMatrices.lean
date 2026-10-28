/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Notation

/-!
# Native zero/one matrices for an Exact Triangle instance

The input contains ordinary unsigned residues. Each output cell computes its row, middle vertex
and label through charged division/remainder instructions. Cells outside the selected piece are
zero; all other cells test the required modular adjacency. The same seventeen registers serve
the left `n×D` and right `D×n` matrices, with no supplied indexing table.

The X/Y output entries are raw unsigned words `0` and `1`. A consumer using canonical
`Signed.encode` matrix entries must double each entry while copying it into that input and
charge the conversion instruction. Scalar headers, pointers and query coordinates remain raw
unsigned words.

This directly adapts the adjacency formulas in the pinned
[Theorem 17 instance builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean).
The native implementation visits each output cell once; the source clears and then marks cells.

## Main definitions

* `WriteMatrices.Args`: matrix dimensions, residue/piece parameters and memory blocks.
* `WriteMatrices.entry`: the zero/one value at a flat output position.
* `WriteMatrices.program`: fixed native left/right matrix builders.

## Main results

* `WriteMatrices.exec`: complete charged execution and the output/input frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WriteMatrices

open Cslib.WordRAM

/-- Runtime arguments of one matrix-building call. -/
structure Args where
  /-- Residue matrix base. -/
  src : ℕ
  /-- Output matrix base. -/
  dst : ℕ
  /-- Number of vertices in each outer part. -/
  n : ℕ
  /-- Padded middle dimension. -/
  D : ℕ
  /-- Positive modulus. -/
  p : ℕ
  /-- First vertex of the selected piece. -/
  first : ℕ
  /-- Number of vertices in the piece. -/
  length : ℕ
  /-- A–B query residue. -/
  rho : ℕ

/-- Raw unsigned zero/one row-major adjacency. A true side chooses the right `D×n` matrix;
false chooses the left `n×D` matrix. The source residue matrix has shape `n×n`. A signed-matrix
consumer encodes these entries by doubling them. -/
def entry (rightSide : Bool) (A : Args) (R : ℕ → ℕ) (q : ℕ) : ℕ :=
  let line := if rightSide then q % A.n else q / A.D
  let middle := if rightSide then q / A.n else q % A.D
  let label := middle % A.p
  let vertex := middle / A.p
  if vertex < A.length then
    let r := R (line * A.n + A.first + vertex)
    let wanted := if rightSide then (A.p - r) % A.p else (r + A.rho) % A.p
    if label = wanted then 1 else 0
  else 0

/-- Residue input pointer. -/
abbrev src : Fin 17 := 0
/-- Output matrix pointer. -/
abbrev dst : Fin 17 := 1
/-- Outer dimension. -/
abbrev size : Fin 17 := 2
/-- Middle dimension. -/
abbrev dimension : Fin 17 := 3
/-- Modulus. -/
abbrev modulus : Fin 17 := 4
/-- First vertex of the piece. -/
abbrev first : Fin 17 := 5
/-- Piece length. -/
abbrev length : Fin 17 := 6
/-- Query residue. -/
abbrev rho : Fin 17 := 7
/-- Flat output cursor. -/
abbrev idx : Fin 17 := 8
/-- Number of output cells. -/
abbrev area : Fin 17 := 9
/-- Selected source row. -/
abbrev line : Fin 17 := 10
/-- Selected vertex within the piece. -/
abbrev vertex : Fin 17 := 11
/-- Middle label. -/
abbrev label : Fin 17 := 12
/-- Address temporary. -/
abbrev addr : Fin 17 := 13
/-- Residue and output value temporary. -/
abbrev value : Fin 17 := 14
/-- Constant zero. -/
abbrev zero : Fin 17 := 15
/-- Constant one. -/
abbrev one : Fin 17 := 16

/-- The eight runtime arguments occupy registers 0–7. -/
structure Entry (A : Args) (x : Data 17) : Prop where
  /-- Source pointer. -/
  src : x.regs src = A.src
  /-- Destination pointer. -/
  dst : x.regs dst = A.dst
  /-- Outer dimension. -/
  size : x.regs size = A.n
  /-- Middle dimension. -/
  dimension : x.regs dimension = A.D
  /-- Modulus. -/
  modulus : x.regs modulus = A.p
  /-- First vertex. -/
  first : x.regs first = A.first
  /-- Piece length. -/
  length : x.regs length = A.length
  /-- Query residue. -/
  rho : x.regs rho = A.rho

/-- Compute the source row and decode the middle label using actual arithmetic instructions. -/
def indices (rightSide : Bool) : Code .standard 17 :=
  if rightSide then ram[
    line ← idx % size; vertex ← idx / size; label ← vertex % modulus;
    vertex ← vertex / modulus ]
  else ram[
    line ← idx / dimension; vertex ← idx % dimension; label ← vertex % modulus;
    vertex ← vertex / modulus ]

/-- Read the selected residue and form its required label. -/
def readLabel (rightSide : Bool) : Code .standard 17 :=
  .seq (ram[ addr ← line * size; addr ← addr + first; addr ← addr + vertex;
    addr ← src + addr; value ← *addr ])
    (if rightSide then ram[ value ← modulus - value; value ← value % modulus ]
    else ram[ value ← value + rho; value ← value % modulus ])

/-- Write one zero/one cell and increment the flat cursor. -/
def body (rightSide : Bool) : Code .standard 17 :=
  .seq (indices rightSide)
    (.seq (.branch (.lt vertex length)
      (.seq (readLabel rightSide)
        (.branch (.eq label value) (.op (.copy value one)) (.op (.copy value zero))))
      (.op (.copy value zero)))
      (ram[ addr ← dst + idx; *addr ← value; idx ← idx + one ]))

/-- The complete builder initializes constants and visits all output positions once. -/
def program (rightSide : Bool) : Code .standard 17 :=
  .seq (ram[ zero ← #0; one ← #1; idx ← #0; area ← size * dimension ])
    (.loop (.lt idx area) (body rightSide))

/-- The instruction graph has fixed size and never reads the physical word width. -/
theorem program_fixed (rightSide : Bool) :
    (program rightSide).size ≤ 64 ∧ ¬(program rightSide).ReadsWidth := by
  cases rightSide <;> decide

private theorem entry_of_regs {A : Args} {x y : Data 17} (hx : Entry A x)
    (h : ∀ i : Fin 17, i.val < 8 → y.regs i = x.regs i) : Entry A y :=
  ⟨(h src (by decide)).trans hx.src, (h dst (by decide)).trans hx.dst,
    (h size (by decide)).trans hx.size, (h dimension (by decide)).trans hx.dimension,
    (h modulus (by decide)).trans hx.modulus, (h first (by decide)).trans hx.first,
    (h length (by decide)).trans hx.length, (h rho (by decide)).trans hx.rho⟩

private theorem exec_indices {w q : ℕ} (side : Bool) (A : Args) (x : Data 17)
    (hx : Entry A x) (hq : x.regs idx = q) (hfit : Fits w q) :
    ∃ y, ExecWithin w (indices side) x y 4 ∧ Entry A y ∧
      y.regs idx = q ∧ y.regs line = (if side then q % A.n else q / A.D) ∧
      y.regs vertex = (if side then q / A.n else q % A.D) / A.p ∧
      y.regs label = (if side then q / A.n else q % A.D) % A.p ∧
      y.regs one = x.regs one ∧ y.regs zero = x.regs zero ∧ y.mem = x.mem := by
  have hdn : Fits w (q / A.n) := hfit.of_le (Nat.div_le_self ..)
  have hmn : Fits w (q % A.n) := hfit.of_le (Nat.mod_le ..)
  have hdd : Fits w (q / A.D) := hfit.of_le (Nat.div_le_self ..)
  have hmd : Fits w (q % A.D) := hfit.of_le (Nat.mod_le ..)
  have hdnp : Fits w (q / A.n / A.p) := hdn.of_le (Nat.div_le_self ..)
  have hmnp : Fits w (q / A.n % A.p) := hdn.of_le (Nat.mod_le ..)
  have hmdp : Fits w (q % A.D / A.p) := hmd.of_le (Nat.div_le_self ..)
  have hmmp : Fits w (q % A.D % A.p) := hmd.of_le (Nat.mod_le ..)
  let rowValue := if side then q % A.n else q / A.D
  let middleValue := if side then q / A.n else q % A.D
  let y := x.set line rowValue |>.set vertex middleValue
    |>.set label (middleValue % A.p) |>.set vertex (middleValue / A.p)
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · cases side <;>
      ram_eval [indices, y, rowValue, middleValue, hq, hx.size, hx.dimension, hx.modulus,
        hdn, hmn, hdd, hmd, hdnp, hmnp, hmdp, hmmp, line, vertex, label, idx, size,
        dimension, modulus, Fin.mk.injEq]
  · apply entry_of_regs hx
    intro i hi
    have hl : i ≠ line := by intro h; subst i; change 10 < 8 at hi; omega
    have hv : i ≠ vertex := by intro h; subst i; change 11 < 8 at hi; omega
    have hb : i ≠ label := by intro h; subst i; change 12 < 8 at hi; omega
    simp only [y, Data.set_regs, Function.update_of_ne hl, Function.update_of_ne hv,
      Function.update_of_ne hb]
  · simp +decide [y, idx, line, vertex, label, hq]
  · simp +decide [y, rowValue, line, vertex, label]
  · simp [y, middleValue]
  · simp +decide [y, middleValue, line, vertex, label]
  · simp +decide [y, one, line, vertex, label]
  · simp +decide [y, zero, line, vertex, label]

private theorem exec_readLabel {w row v : ℕ} (side : Bool) (A : Args) (R : ℕ → ℕ)
    (x : Data 17) (hx : Entry A x)
    (hrow : x.regs line = row) (hv : x.regs vertex = v)
    (hpoint : row * A.n + A.first + v < A.n * A.n)
    (hR : ∀ i < A.n * A.n, R i < A.p)
    (hinput : ∀ i < A.n * A.n, x.mem (A.src + i) = R i)
    (hs : Fits w (A.src + A.n * A.n)) (hp : Fits w (2 * A.p)) (hrho : A.rho < A.p) :
    ∃ y, ExecWithin w (readLabel side) x y 7 ∧
      y.regs value = (if side then (A.p - R (row * A.n + A.first + v)) % A.p
        else (R (row * A.n + A.first + v) + A.rho) % A.p) ∧
      (∀ i, i ≠ addr → i ≠ value → y.regs i = x.regs i) ∧ y.mem = x.mem := by
  let pos := row * A.n + A.first + v
  have hpos : pos < A.n * A.n := hpoint
  have hkey := hR pos hpos
  have hr := hinput pos hpos
  have hmul : Fits w (row * A.n) := hs.of_le (by dsimp [pos] at hpos; omega)
  have hfirst : Fits w (row * A.n + A.first) := hs.of_le (by dsimp [pos] at hpos; omega)
  have hindex : Fits w pos := hs.of_le (by omega)
  have haddr : Fits w (A.src + pos) := hs.of_le (by omega)
  have hsub : Fits w (A.p - R pos) := hp.of_le (by omega)
  have hadd : Fits w (R pos + A.rho) := hp.of_le (by omega)
  have hmodsub : Fits w ((A.p - R pos) % A.p) := hsub.of_le (Nat.mod_le ..)
  have hmodadd : Fits w ((R pos + A.rho) % A.p) := hadd.of_le (Nat.mod_le ..)
  let z := x.set addr (row * A.n) |>.set addr (row * A.n + A.first)
    |>.set addr pos |>.set addr (A.src + pos) |>.set value (R pos)
  let t := if side then A.p - R pos else R pos + A.rho
  let y := z.set value t |>.set value (t % A.p)
  refine ⟨y, ?_, ?_, ?_, rfl⟩
  · cases side <;>
      ram_eval [readLabel, z, t, y, hrow, hv, hx.size, hx.first, hx.src, hx.modulus, hx.rho,
        hmul, hfirst, hindex, haddr, hsub, hadd, hmodsub, hmodadd, hr, pos, line, vertex,
        size, first, src, modulus, rho, addr, value, Fin.mk.injEq]
  · cases side <;> simp [y, t, pos]
  · intro i hi hv
    simp only [y, z, Data.set_regs, Function.update_of_ne hi, Function.update_of_ne hv]

private theorem body_preserves (side : Bool) : ∀ i : Fin 17,
    (i.val < 8 ∨ i = area ∨ i = one ∨ i = zero) → (body side).Preserves i := by
  cases side <;> decide

private theorem exec_body {w q : ℕ} (side : Bool) (A : Args) (R : ℕ → ℕ)
    (x : Data 17) (hx : Entry A x) (hq : x.regs idx = q)
    (ho : x.regs one = 1) (hz : x.regs zero = 0) (hlt : q < A.n * A.D)
    (hrho : A.rho < A.p) (hpiece : A.first + A.length ≤ A.n)
    (hR : ∀ i < A.n * A.n, R i < A.p)
    (hinput : ∀ i < A.n * A.n, x.mem (A.src + i) = R i)
    (hsrc : Fits w (A.src + A.n * A.n)) (hdst : Fits w (A.dst + A.n * A.D))
    (hmod : Fits w (2 * A.p)) :
    ∃ y, ExecWithin w (body side) x y 18 ∧ y.regs idx = q + 1 ∧
      y.mem = Function.update x.mem (A.dst + q) (entry side A R q) := by
  have hqfit : Fits w q := hdst.of_le (by omega)
  obtain ⟨b, hb, hba, hbi, hbl, hbv, hbb, hbo, hbz, hbm⟩ :=
    exec_indices side A x hx hq hqfit
  let row := if side then q % A.n else q / A.D
  let mid := if side then q / A.n else q % A.D
  let v := mid / A.p
  let σ := mid % A.p
  let gate : Code .standard 17 := .branch (.lt vertex length)
    (.seq (readLabel side)
      (.branch (.eq label value) (.op (.copy value one)) (.op (.copy value zero))))
    (.op (.copy value zero))
  have hgate : ∃ z, ExecWithin w gate b z 11 ∧ z.regs value = entry side A R q ∧
      z.regs idx = q ∧ z.regs one = 1 ∧ z.mem = x.mem := by
    by_cases hv : v < A.length
    · have hn : 0 < A.n := by
        by_contra h
        have hn : A.n = 0 := by omega
        simp only [hn, Nat.zero_mul] at hlt
        omega
      have hD : 0 < A.D := by
        by_contra h
        have hD : A.D = 0 := by omega
        simp only [hD, Nat.mul_zero] at hlt
        omega
      have hrow : row < A.n := by
        cases side
        · exact (Nat.div_lt_iff_lt_mul hD).mpr hlt
        · exact Nat.mod_lt _ hn
      have hpoint : row * A.n + A.first + v < A.n * A.n := by
        have hb := Nat.mul_le_mul_right A.n (Nat.succ_le_of_lt hrow)
        rw [Nat.succ_mul] at hb
        omega
      obtain ⟨c, hc, hcv, hcr, hcm⟩ := exec_readLabel side A R b hba hbl hbv hpoint hR
        (by simpa only [hbm] using hinput) hsrc hmod hrho
      let wanted := if side then (A.p - R (row * A.n + A.first + v)) % A.p
        else (R (row * A.n + A.first + v) + A.rho) % A.p
      have hcl : c.regs label = σ := (hcr label (by decide) (by decide)).trans hbb
      have hci : c.regs idx = q := (hcr idx (by decide) (by decide)).trans hbi
      have hco : c.regs one = 1 := (hcr one (by decide) (by decide)).trans (hbo.trans ho)
      have hcz : c.regs zero = 0 := (hcr zero (by decide) (by decide)).trans (hbz.trans hz)
      let z := c.set value (if σ = wanted then 1 else 0)
      have hchoose : ExecWithin (B := .standard) w
          (.branch (.eq label value) (.op (.copy value one)) (.op (.copy value zero))) c z 3 := by
        by_cases h : σ = wanted <;>
          ram_eval [z, hcl, hcv, hco, hcz, h, wanted, row, v, mid, σ, label, value, one,
            zero, Fin.mk.injEq]
      have hcond : (Cond.lt vertex length).Holds b := by
        simpa only [Cond.holds_lt, hbv, hba.length] using hv
      refine ⟨z, ?_, ?_, ?_, ?_, hcm.trans hbm⟩
      · exact (ExecWithin.branch_pos hcond (hc.seq hchoose)).mono (by omega)
      · simp only [z, Data.set_regs, Function.update_self, entry, row, mid, v, σ, hv,
          ↓reduceIte, wanted]
      · simpa +decide [z, idx, value] using hci
      · simpa +decide [z, one, value] using hco
    · have hcond : ¬(Cond.lt vertex length).Holds b := by
        simpa only [Cond.holds_lt, hbv, hba.length] using hv
      refine ⟨b.set value 0, ?_, ?_, ?_, ?_, hbm⟩
      · have he : ExecWithin w gate b (b.set value 0) 3 := ExecWithin.branch_neg hcond
          (show ExecWithin w (.op (.copy value zero)) b (b.set value 0) 1 from by
            simpa only [hbz, hz] using (ExecWithin.copy (x := b) (d := value) (s := zero)))
        exact he.mono (by omega)
      · simp only [Data.set_regs, Function.update_self, entry, mid, v, hv, ↓reduceIte]
      · simpa +decide [idx, value] using hbi
      · simpa +decide [one, value] using hbo.trans ho
  obtain ⟨z, hzg, hzv, hzi, hzo, hzm⟩ := hgate
  have hzd : z.regs dst = A.dst :=
    (hzg.regs_eq (by cases side <;> decide)).trans hba.dst
  have haddr : Fits w (A.dst + q) := hdst.of_le (by omega)
  have hinc : Fits w (q + 1) := hdst.of_le (by omega)
  let y := (z.set addr (A.dst + q)).write (A.dst + q) (entry side A R q)
    |>.set idx (q + 1)
  have htail : ExecWithin w
      (ram[ addr ← dst + idx; *addr ← value; idx ← idx + one ]) z y 3 := by
    ram_eval [y, hzd, hzi, hzv, hzo, haddr, hinc, addr, dst, idx, value, one, Fin.mk.injEq]
  refine ⟨y, ?_, by simp [y], ?_⟩
  · simpa only [body, gate, Nat.reduceAdd] using hb.seq (hzg.seq htail)
  · change Function.update z.mem (A.dst + q) (entry side A R q) = _
    rw [hzm]

/-- Construct every entry of a left or right instance matrix in `20nD+6` native instructions,
excluding the halt. The source is an actual residue array below the output. All cells outside
the output block and all eight arguments are preserved. No adjacency table is supplied. -/
theorem exec {w : ℕ} (side : Bool) (A : Args) (R : ℕ → ℕ) (x : Data 17)
    (hx : Entry A x) (hrho : A.rho < A.p) (hpiece : A.first + A.length ≤ A.n)
    (hR : ∀ i < A.n * A.n, R i < A.p)
    (hinput : ∀ i < A.n * A.n, x.mem (A.src + i) = R i)
    (hsrc : Fits w (A.src + A.n * A.n)) (hdst : Fits w (A.dst + A.n * A.D))
    (hmod : Fits w (2 * A.p)) (hdisj : A.src + A.n * A.n ≤ A.dst) :
    ∃ y, ExecWithin w (program side) x y (20 * (A.n * A.D) + 6) ∧ Entry A y ∧
      y.regs idx = A.n * A.D ∧
      (Block.mk A.dst (A.n * A.D)).Realizes y.mem (fun i => entry side A R i) ∧
      (∀ a, ¬(Block.mk A.dst (A.n * A.D)).Owns a → y.mem a = x.mem a) := by
  let I (y : Data 17) : Prop := Entry A y ∧ y.regs area = A.n * A.D ∧
    y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs idx ≤ A.n * A.D ∧
    (∀ j < y.regs idx, y.mem (A.dst + j) = entry side A R j) ∧
    (∀ a, ¬(A.dst ≤ a ∧ a < A.dst + y.regs idx) → y.mem a = x.mem a)
  have hbody (y : Data 17) (hy : I y) (hc : (Cond.lt idx area).Holds y) :
      ∃ z, ExecWithin w (body side) y z 18 ∧ I z ∧
        A.n * A.D - z.regs idx < A.n * A.D - y.regs idx := by
    obtain ⟨hyp, hya, hyo, hyz, hyi, hym, hyout⟩ := hy
    have hlt : y.regs idx < A.n * A.D := by
      simpa only [Cond.holds_lt, hya] using hc
    have hyinput : ∀ i < A.n * A.n, y.mem (A.src + i) = R i := by
      intro i hi
      rw [hyout _ (by omega)]
      exact hinput i hi
    obtain ⟨z, he, hzi, hzm⟩ := exec_body side A R y hyp rfl hyo hyz hlt
      hrho hpiece hR hyinput hsrc hdst hmod
    have hpres (i : Fin 17) (hi : i.val < 8 ∨ i = area ∨ i = one ∨ i = zero) :
        z.regs i = y.regs i := he.regs_eq (body_preserves side i hi)
    refine ⟨z, he, ⟨entry_of_regs hyp (fun i hi => hpres i (Or.inl hi)),
      (hpres area (by simp)).trans hya, (hpres one (by simp)).trans hyo,
      (hpres zero (by simp)).trans hyz, by omega, ?_, ?_⟩, by omega⟩
    · intro j hj
      rw [hzm]
      by_cases h : j = y.regs idx
      · subst j
        exact Function.update_self ..
      · rw [Function.update_of_ne (by omega)]
        exact hym j (by omega)
    · intro a ha
      rw [hzm, Function.update_of_ne (by omega)]
      exact hyout a (by omega)
  have h1 : Fits w 1 := hmod.of_le (by omega)
  have ha : Fits w (A.n * A.D) := hdst.of_le (by omega)
  let x₀ := x.set zero 0 |>.set one 1 |>.set idx 0 |>.set area (A.n * A.D)
  have hx₀ : I x₀ := by
    refine ⟨entry_of_regs hx ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hz : i ≠ zero := by intro h; subst i; change 15 < 8 at hi; omega
      have ho : i ≠ one := by intro h; subst i; change 16 < 8 at hi; omega
      have hn : i ≠ idx := by intro h; subst i; change 8 < 8 at hi; omega
      have ha : i ≠ area := by intro h; subst i; change 9 < 8 at hi; omega
      simp only [x₀, Data.set_regs, Function.update_of_ne hz, Function.update_of_ne ho,
        Function.update_of_ne hn, Function.update_of_ne ha]
    · simp [x₀]
    · simp +decide [x₀, one, idx, area]
    · simp +decide [x₀, zero, one, idx, area]
    · simp +decide [x₀, idx, area]
    · intro j hj
      simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, area, ↓reduceIte] at hj
      omega
    · intro a _
      rfl
  have hinit : ExecWithin w
      (ram[ zero ← #0; one ← #1; idx ← #0; area ← size * dimension ]) x x₀ 4 := by
    ram_eval [x₀, hx.size, hx.dimension, ha, h1, zero, one, idx, area, size, dimension,
      Fin.mk.injEq]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => A.n * A.D - y.regs idx) hbody hx₀
  obtain ⟨hyp, hya, -, -, hyi, hym, hyout⟩ := hy
  have hend : y.regs idx = A.n * A.D := by
    simp only [Cond.holds_lt, hya] at hc
    omega
  refine ⟨y, ?_, hyp, hend, ?_, ?_⟩
  · convert hinit.seq he using 1
    · rfl
    · simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, area, ↓reduceIte]
      omega
  · intro i
    exact hym i (by simpa only [hend] using i.isLt)
  · intro a ha
    exact hyout a (by simpa only [hend, Block.Owns] using ha)

end Cslib.Algorithms.WordRAM.ExactTriangle.WriteMatrices
