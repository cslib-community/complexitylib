/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Weight

/-!
# One cell of the three Convolution-3SUM matrices

This directly adapts `fillCells` of Anthropic's pinned graph builder at
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, using native unsigned word-RAM instructions.
The row and column, all three input indices, and the three destination addresses are computed
by the program. A negative BC index is replaced with the negative sentinel `-1`: both select
the filler. Registers 22 through 25 are additional scratch; registers 14 through 21 belong to
the caller. The AB and BC destinations follow the input, preserving it for subsequent reads.
The final AC write may alias the input; the complete matrix loop uses disjoint blocks.

## Main definitions

* `Cell.step`: compute and write one cell of each matrix.

## Main results

* `Cell.exec_step`: exact memory effect and a constant charged native instruction bound.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Cell

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum (pick)

/-- Current row-major cell. -/
abbrev cell : Fin 28 := 14
/-- Number of vertices per part. -/
abbrev side : Fin 28 := 15
/-- Instance number. -/
abbrev inst : Fin 28 := 16
/-- Base address of matrix AB. -/
abbrev matAB : Fin 28 := 17
/-- Base address of matrix BC. -/
abbrev matBC : Fin 28 := 18
/-- Base address of matrix AC. -/
abbrev matAC : Fin 28 := 19
/-- Input length. -/
abbrev len : Fin 28 := 10
/-- Input base address. -/
abbrev base : Fin 28 := 11
/-- Signed encoded filler. -/
abbrev filler : Fin 28 := 12

/-- Encoded source index. -/
abbrev index : Fin 28 := 9
/-- Current destination address. -/
abbrev dest : Fin 28 := 13
/-- Saved encoded filler. -/
abbrev saved : Fin 28 := 22
/-- Encoded negation of the filler. -/
abbrev negFill : Fin 28 := 23
/-- Computed row of the current cell. -/
abbrev row : Fin 28 := 24
/-- Computed column of the current cell. -/
abbrev col : Fin 28 := 25
/-- Place the fourteen weight registers at the start of the cell register file. -/
def embedding (i : Fin 14) : Fin 28 := ⟨i.val, by omega⟩
private theorem embedding_injective : Function.Injective embedding := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 28 => k.val) h

/-- The existing weight kernel embedded in the larger register file. -/
def writeWeight (negate : Bool) : Code .standard 28 :=
  (Weight.store negate).rename embedding

private theorem weight_preserves (negate : Bool) :
    ∀ i : Fin 28, 9 ≤ i.val → (writeWeight negate).Preserves i := by
  cases negate <;> decide

private theorem exec_weight {w N b d : ℕ} {μ : ℕ → ℤ} {fill z : ℤ}
    (negate : Bool) (x : Data 28)
    (hindex : x.regs index = encode z) (hlen : x.regs len = N)
    (hbase : x.regs base = b) (hfiller : x.regs filler = encode fill)
    (hdest : x.regs dest = d) (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hz : GenericRAM.Signed.Fits w z) (hfill : GenericRAM.Signed.Fits w fill)
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i)) (haddr : Fits (w + 2) (b + N)) :
    ∃ y, ExecWithin (w + 2) (writeWeight negate) x y 28 ∧
      y.mem = Function.update x.mem d
        (encode (if negate then -pick N μ fill z else pick N μ fill z)) ∧
      ∀ i : Fin 28, 9 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨y, he, hm, -⟩ := Weight.exec_store negate (x.comap embedding)
    hindex hlen hbase hfiller hdest hmem hz hfill hμ haddr
  have hr := he.rename embedding_injective
  exact ⟨_, hr, hm, fun i hi => hr.regs_eq (weight_preserves negate i hi)⟩

/-- Save the filler, compute the coordinates and prepare its negation operands. -/
def prepareSetup : Code .standard 28 := ram[
  saved ← filler; row ← cell / side; col ← cell % side; left ← #0; right ← filler ]

/-- Compute the row and column, save the filler, and form its signed negation. -/
def prepare : Code .standard 28 := ram[
  ⟪prepareSetup⟫; ⟪subtract⟫; negFill ← result ]

/-- Write the AB cell, including encoding its index and calculating its address. -/
def setupAB : Code .standard 28 := ram[ index ← cell + cell; dest ← matAB + cell ]

/-- Write the AB cell after computing its index and destination. -/
def putAB : Code .standard 28 := ram[ ⟪setupAB⟫; ⟪writeWeight false⟫ ]

/-- Write BC, testing for a negative index before unsigned subtraction. -/
def setupBC : Code .standard 28 := ram[
  index ← col * side; index ← index + inst;
  if index < row then [ index ← #3 ] else [
    index ← index - row; index ← index + index ];
  dest ← matBC + cell ]

/-- Write BC after computing its guarded signed index and destination. -/
def putBC : Code .standard 28 := ram[ ⟪setupBC⟫; ⟪writeWeight false⟫ ]

/-- Write AC with negated filler before negating the selected value, then restore the filler. -/
def setupAC : Code .standard 28 := ram[
  index ← row + col; index ← index * side; index ← index + inst;
  index ← index + index; dest ← matAC + cell; filler ← negFill ]

/-- Write AC and restore the caller's positive filler. -/
def putAC : Code .standard 28 := ram[
  ⟪setupAC⟫; ⟪writeWeight true⟫; filler ← saved ]

/-- Compute and write all three entries at the current row-major cell. -/
def step : Code .standard 28 := ram[
  ⟪prepare⟫; ⟪putAB⟫; ⟪putBC⟫; ⟪putAC⟫ ]

private theorem step_preserves : ∀ i : Fin 28,
    i.val = 10 ∨ i.val = 11 ∨ (14 ≤ i.val ∧ i.val ≤ 21) ∨ 26 ≤ i.val →
      step.Preserves i := by decide

private theorem signed_nat_mono {w H k : ℕ} (hH : GenericRAM.Signed.Fits w (H : ℤ))
    (hk : k ≤ H) : GenericRAM.Signed.Fits w (k : ℤ) :=
  ⟨hH.1, le_trans (neg_nonpos.mpr (by positivity)) (Nat.cast_nonneg k),
    by have := hH.2.2; omega⟩

private theorem encode_nat (k : ℕ) : encode (k : ℤ) = k + k := by
  simp [encode, two_mul]

private theorem picked_index {N a b : ℕ} {μ : ℕ → ℤ} {F : ℤ} :
    pick N μ F (if a < b then -1 else (a - b : ℕ)) =
      pick N μ F ((a : ℤ) - b) := by
  by_cases h : a < b
  · simp [h, pick]
  · have he : (a - b : ℕ) = (a : ℤ) - b := by omega
    simp only [h, ↓reduceIte, he]

private theorem prepare_preserves : ∀ i : Fin 28,
    (9 ≤ i.val ∧ i.val ≤ 21) ∨ 26 ≤ i.val → prepare.Preserves i := by decide

private theorem exec_prepare {w q t : ℕ} {F : ℤ} (x : Data 28)
    (hq : x.regs cell = q) (ht : x.regs side = t) (hf : x.regs filler = encode F)
    (hrow : Fits (w + 2) (q / t)) (hcol : Fits (w + 2) (q % t))
    (hF : GenericRAM.Signed.Fits w F) :
    ∃ y, ExecWithin (w + 2) prepare x y 23 ∧ y.mem = x.mem ∧
      y.regs row = q / t ∧ y.regs col = q % t ∧
      y.regs saved = encode F ∧ y.regs negFill = encode (-F) ∧
      ∀ i : Fin 28, (9 ≤ i.val ∧ i.val ≤ 21) ∨ 26 ≤ i.val → y.regs i = x.regs i := by
  let z := ((((x.set saved (encode F)).set row (q / t)).set col (q % t)).set left 0).set right
    (encode F)
  have hp : ExecWithin (w + 2)
      prepareSetup x z 5 := by
    ram_eval [prepareSetup, z, hf, hq, ht, hrow, hcol, saved, row, col, cell, side, filler,
      left, right, Fin.mk.injEq]
  obtain ⟨u, hu, hur, hum, hureg⟩ := exec_subtract (GenericRAM.Signed.fits_zero hF.1) hF z
    (by simp +decide [z, left, right, encode])
    (by simp [z])
  let y := u.set negFill (encode (-F))
  have he : ExecWithin (w + 2) prepare x y 23 := by
    have hc : ExecWithin (B := .standard) (w + 2) (.op (.copy negFill result)) u y 1 := by
      simpa only [y, hur, GenericRAM.Signed.Arithmetic.eval, zero_sub] using
        (ExecWithin.copy (B := .standard) (w := w + 2) (x := u) (d := negFill) (s := result))
    exact hp.seq (hu.seq hc)
  refine ⟨y, he, hum, ?_, ?_, ?_, ?_,
    fun i hi => he.regs_eq (prepare_preserves i hi)⟩
  · have hr := hureg row (Or.inr (by decide))
    simpa +decide [y, z, row, negFill, left, right, col] using hr
  · have hc := hureg col (Or.inr (by decide))
    simpa +decide [y, z, col, negFill, left, right] using hc
  · have hs := hureg saved (Or.inr (by decide))
    simpa +decide [y, z, saved, negFill, left, right, row, col] using hs
  · simp [y]

private theorem ab_preserves : ∀ i : Fin 28,
    10 ≤ i.val → i.val ≠ 13 → putAB.Preserves i := by decide

private theorem bc_preserves : ∀ i : Fin 28,
    10 ≤ i.val → i.val ≠ 13 → putBC.Preserves i := by decide

private theorem ac_preserves : ∀ i : Fin 28,
    10 ≤ i.val → i.val ≠ 12 → i.val ≠ 13 → putAC.Preserves i := by decide

private theorem exec_AB {w N b d q : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (hmat : x.regs matAB = d)
    (hlen : x.regs len = N) (hbase : x.regs base = b) (hfiller : x.regs filler = encode F)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hq : GenericRAM.Signed.Fits w (q : ℤ)) (hF : GenericRAM.Signed.Fits w F)
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N)) (hd : Fits (w + 2) (d + q)) :
    ∃ y, ExecWithin (w + 2) putAB x y 30 ∧
      y.mem = Function.update x.mem (d + q) (encode (pick N μ F q)) ∧
      ∀ i : Fin 28, 10 ≤ i.val → i.val ≠ 13 → y.regs i = x.regs i := by
  let z := (x.set index (q + q)).set dest (d + q)
  have hqfit : Fits (w + 2) (q + q) := by
    simpa only [encode_nat] using (encode_fits hq).mono (by omega : w + 1 ≤ w + 2)
  have hp : ExecWithin (w + 2) setupAB x z 2 := by
    ram_eval [setupAB, z, hcell, hmat, hqfit, hd, cell, matAB, index, dest, Fin.mk.injEq]
  obtain ⟨y, hy, hym, -⟩ := exec_weight (d := d + q) false z
    (by simp +decide [z, index, dest, encode_nat])
    (by simpa +decide [z, len, index, dest] using hlen)
    (by simpa +decide [z, base, index, dest] using hbase)
    (by simpa +decide [z, filler, index, dest] using hfiller)
    (by simp [z]) hmem hq hF hμ haddr
  have he : ExecWithin (w + 2) putAB x y 30 := hp.seq hy
  exact ⟨y, he, hym, fun i hi hne => he.regs_eq (ab_preserves i hi hne)⟩

private theorem exec_BC {w N b d q r c t s : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (hmat : x.regs matBC = d)
    (hrow : x.regs row = r) (hcol : x.regs col = c)
    (ht : x.regs side = t) (hs : x.regs inst = s)
    (hlen : x.regs len = N) (hbase : x.regs base = b) (hfiller : x.regs filler = encode F)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hidx : GenericRAM.Signed.Fits w ((c * t + s : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w F) (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N)) (hd : Fits (w + 2) (d + q)) :
    ∃ y, ExecWithin (w + 2) putBC x y 35 ∧
      y.mem = Function.update x.mem (d + q) (encode (pick N μ F ((c * t + s : ℕ) - (r : ℤ)))) ∧
      ∀ i : Fin 28, 10 ≤ i.val → i.val ≠ 13 → y.regs i = x.regs i := by
  let a := c * t + s
  let ix : ℤ := if a < r then -1 else (a - r : ℕ)
  let z₀ := (x.set index (c * t)).set index a
  let z₁ := if a < r then z₀.set index 3 else
    (z₀.set index (a - r)).set index ((a - r) + (a - r))
  let z := z₁.set dest (d + q)
  have hfit : Fits (w + 2) (a + a) := by
    simpa only [encode_nat] using (encode_fits hidx).mono (by omega : w + 1 ≤ w + 2)
  have hmfit : Fits (w + 2) (c * t) := hfit.of_le (by dsimp [a]; omega)
  have hafit : Fits (w + 2) a := hfit.of_le (by omega)
  have hdfit : Fits (w + 2) (a - r) := hfit.of_le (by omega)
  have hddfit : Fits (w + 2) ((a - r) + (a - r)) := hfit.of_le (by omega)
  have h3 : Fits (w + 2) 3 := (show Fits 2 3 from by decide).mono (by omega)
  have hp : ExecWithin (w + 2) setupBC x z 7 := by
    by_cases hh : a < r <;>
      ram_eval [setupBC, z, z₁, z₀, hcell, hmat, hrow, hcol, ht, hs, hmfit, hafit,
        hdfit, hddfit, h3, hd, hh, a, cell, matBC, row, col, side, inst, index, dest,
        Fin.mk.injEq]
  have hix : GenericRAM.Signed.Fits w ix := by
    dsimp only [ix]
    split_ifs
    · exact ⟨hidx.1, by have := hidx.2.1; have := hidx.2.2; omega, by have := hidx.2.2; omega⟩
    · exact signed_nat_mono hidx (by dsimp [a]; omega)
  obtain ⟨y, hy, hym, -⟩ := exec_weight (d := d + q) false z
    (by dsimp [z, z₁, ix]; split_ifs <;> simp +decide [index, dest, encode, two_mul])
    (by dsimp [z, z₁, z₀]; split_ifs <;> simpa +decide [len, index, dest] using hlen)
    (by dsimp [z, z₁, z₀]; split_ifs <;> simpa +decide [base, index, dest] using hbase)
    (by dsimp [z, z₁, z₀]; split_ifs <;> simpa +decide [filler, index, dest] using hfiller)
    (by simp [z]) (by dsimp [z, z₁, z₀]; split_ifs <;> exact hmem) hix hF hμ haddr
  have he : ExecWithin (w + 2) putBC x y 35 := hp.seq hy
  refine ⟨y, he, ?_, fun i hi hne => he.regs_eq (bc_preserves i hi hne)⟩
  have hzm : z.mem = x.mem := by dsimp [z, z₁, z₀]; split_ifs <;> rfl
  simpa only [Bool.false_eq_true, ↓reduceIte, ix, a, picked_index, hzm] using hym

private theorem exec_AC {w N b d q r c t s : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (hmat : x.regs matAC = d)
    (hrow : x.regs row = r) (hcol : x.regs col = c)
    (ht : x.regs side = t) (hs : x.regs inst = s)
    (hlen : x.regs len = N) (hbase : x.regs base = b)
    (hsaved : x.regs saved = encode F) (hneg : x.regs negFill = encode (-F))
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hidx : GenericRAM.Signed.Fits w (((r + c) * t + s : ℕ) : ℤ))
    (hpos : 0 < t) (hF : GenericRAM.Signed.Fits w (-F))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N)) (hd : Fits (w + 2) (d + q)) :
    ∃ y, ExecWithin (w + 2) putAC x y 35 ∧
      y.mem = Function.update x.mem (d + q)
        (encode (-pick N μ (-F) ((r + c) * t + s : ℕ))) ∧
      y.regs filler = encode F ∧
      ∀ i : Fin 28, 10 ≤ i.val → i.val ≠ 12 → i.val ≠ 13 → y.regs i = x.regs i := by
  let a := (r + c) * t + s
  let z := (((((x.set index (r + c)).set index ((r + c) * t)).set index a).set index
    (a + a)).set dest (d + q)).set filler (encode (-F))
  have hfit : Fits (w + 2) (a + a) := by
    simpa only [encode_nat] using (encode_fits hidx).mono (by omega : w + 1 ≤ w + 2)
  have hsum : Fits (w + 2) (r + c) := hfit.of_le (by dsimp [a]; nlinarith)
  have hmul : Fits (w + 2) ((r + c) * t) := hfit.of_le (by dsimp [a]; omega)
  have hafit : Fits (w + 2) a := hfit.of_le (by omega)
  have hp : ExecWithin (w + 2) setupAC x z 6 := by
    ram_eval [setupAC, z, hcell, hmat, hrow, hcol, ht, hs, hneg,
      hsum, hmul, hafit, hfit, hd, a, cell, matAC, row, col, side, inst, index, dest,
      filler, negFill, Fin.mk.injEq]
  obtain ⟨u, hu, hum, hureg⟩ := exec_weight (d := d + q) (z := (a : ℤ)) true z
    (by
      simp +decide only [z, Data.set_regs, Function.update_apply, index, dest, filler,
        ↓reduceIte]
      exact (encode_nat a).symm)
    (by simpa +decide [z, len, index, dest, filler] using hlen)
    (by simpa +decide [z, base, index, dest, filler] using hbase)
    (by simp [z]) (by simp +decide [z, dest, filler]) hmem hidx hF hμ haddr
  let y := u.set filler (encode F)
  have hus : u.regs saved = encode F := by
    rw [hureg saved (by decide)]
    simpa +decide [z, saved, index, dest, filler] using hsaved
  have hc : ExecWithin (B := .standard) (w + 2) (.op (.copy filler saved)) u y 1 := by
    simpa only [y, hus] using
      (ExecWithin.copy (B := .standard) (w := w + 2) (x := u) (d := filler) (s := saved))
  have he : ExecWithin (w + 2) putAC x y 35 := hp.seq (hu.seq hc)
  exact ⟨y, he, hum, by simp [y],
    fun i hi h12 h13 => he.regs_eq (ac_preserves i hi h12 h13)⟩

/-- All index computations, three guarded loads, optional signed negation, stores and argument
preparation take at most 128 native instructions. The final halt is excluded. Input cells precede
all destinations; the three writes occur in AB, BC, AC order. -/
theorem exec_step {w N b ab bc ac q t s : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (ht : x.regs side = t) (hs : x.regs inst = s)
    (hab : x.regs matAB = ab) (hbc : x.regs matBC = bc) (hac : x.regs matAC = ac)
    (hlen : x.regs len = N) (hbase : x.regs base = b) (hf : x.regs filler = encode F)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hq : q < t * t) (hidx : GenericRAM.Signed.Fits w ((2 * (t * t) + s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w F) (hnF : GenericRAM.Signed.Fits w (-F))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N))
    (habfit : Fits (w + 2) (ab + q)) (hbcfit : Fits (w + 2) (bc + q))
    (hacfit : Fits (w + 2) (ac + q))
    (hbelowAB : b + N ≤ ab) (hbelowBC : b + N ≤ bc) :
    ∃ y, ExecWithin (w + 2) step x y 128 ∧
      y.mem = Function.update (Function.update (Function.update x.mem
        (ab + q) (encode (pick N μ F q)))
        (bc + q) (encode (pick N μ F ((q % t * t + s : ℕ) - ((q / t : ℕ) : ℤ)))))
        (ac + q) (encode (-pick N μ (-F) ((q / t + q % t) * t + s : ℕ))) ∧
      y.regs filler = x.regs filler ∧
      ∀ i : Fin 28, i.val = 10 ∨ i.val = 11 ∨
        (14 ≤ i.val ∧ i.val ≤ 21) ∨ 26 ≤ i.val → y.regs i = x.regs i := by
  have htpos : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hrow : q / t < t := Nat.div_lt_of_lt_mul hq
  have hcol : q % t < t := Nat.mod_lt q htpos
  have hnat (k : ℕ) (hk : k ≤ 2 * (t * t) + s + 1) : GenericRAM.Signed.Fits w (k : ℤ) :=
    signed_nat_mono hidx hk
  have hfits (k : ℕ) (hk : k ≤ 2 * (t * t) + s + 1) : Fits (w + 2) k :=
    ((encode_fits (hnat k hk)).mono (by omega)).of_le (by rw [encode_nat]; omega)
  obtain ⟨p, hp, hpm, hpr, hpc, hpF, hpnF, hpreg⟩ := exec_prepare x hcell ht hf
    (hfits _ (by nlinarith)) (hfits _ (by nlinarith)) hF
  have hprg (i : Fin 28) (hi : 9 ≤ i.val ∧ i.val ≤ 21) : p.regs i = x.regs i :=
    hpreg i (Or.inl hi)
  obtain ⟨a, ha, ham, hareg⟩ := exec_AB p
    ((hprg cell (by decide)).trans hcell) ((hprg matAB (by decide)).trans hab)
    ((hprg len (by decide)).trans hlen) ((hprg base (by decide)).trans hbase)
    ((hprg filler (by decide)).trans hf) (by simpa only [hpm] using hmem)
    (hnat _ (by omega)) hF hμ haddr habfit
  have hamem : ∀ i < N, a.mem (b + i) = encode (μ i) := by
    intro i hi
    rw [ham, Function.update_of_ne (by omega), hpm]
    exact hmem i hi
  have harg (i : Fin 28) (hi : 10 ≤ i.val) (hne : i.val ≠ 13) : a.regs i = p.regs i :=
    hareg i hi hne
  obtain ⟨v, hv, hvm, hvreg⟩ := exec_BC a
    ((harg cell (by decide) (by decide)).trans ((hprg cell (by decide)).trans hcell))
    ((harg matBC (by decide) (by decide)).trans ((hprg matBC (by decide)).trans hbc))
    ((harg row (by decide) (by decide)).trans hpr)
    ((harg col (by decide) (by decide)).trans hpc)
    ((harg side (by decide) (by decide)).trans ((hprg side (by decide)).trans ht))
    ((harg inst (by decide) (by decide)).trans ((hprg inst (by decide)).trans hs))
    ((harg len (by decide) (by decide)).trans ((hprg len (by decide)).trans hlen))
    ((harg base (by decide) (by decide)).trans ((hprg base (by decide)).trans hbase))
    ((harg filler (by decide) (by decide)).trans ((hprg filler (by decide)).trans hf))
    hamem (hnat _ (by nlinarith)) hF hμ haddr hbcfit
  have hvmem : ∀ i < N, v.mem (b + i) = encode (μ i) := by
    intro i hi
    rw [hvm, Function.update_of_ne (by omega)]
    exact hamem i hi
  have hvrg (i : Fin 28) (hi : 10 ≤ i.val) (hne : i.val ≠ 13) : v.regs i = p.regs i :=
    (hvreg i hi hne).trans (harg i hi hne)
  obtain ⟨y, hy, hym, hyf, -⟩ := exec_AC v
    ((hvrg cell (by decide) (by decide)).trans ((hprg cell (by decide)).trans hcell))
    ((hvrg matAC (by decide) (by decide)).trans ((hprg matAC (by decide)).trans hac))
    ((hvrg row (by decide) (by decide)).trans hpr)
    ((hvrg col (by decide) (by decide)).trans hpc)
    ((hvrg side (by decide) (by decide)).trans ((hprg side (by decide)).trans ht))
    ((hvrg inst (by decide) (by decide)).trans ((hprg inst (by decide)).trans hs))
    ((hvrg len (by decide) (by decide)).trans ((hprg len (by decide)).trans hlen))
    ((hvrg base (by decide) (by decide)).trans ((hprg base (by decide)).trans hbase))
    ((hvrg saved (by decide) (by decide)).trans hpF)
    ((hvrg negFill (by decide) (by decide)).trans hpnF)
    hvmem (hnat _ (by nlinarith)) htpos hnF hμ haddr hacfit
  have he : ExecWithin (w + 2) step x y 128 :=
    (hp.seq (ha.seq (hv.seq hy))).mono (by decide : 23 + (30 + (35 + 35)) ≤ 128)
  refine ⟨y, he, ?_, hyf.trans hf.symm, fun i hi => he.regs_eq (step_preserves i hi)⟩
  rw [hym, hvm, ham, hpm]

end Cslib.Algorithms.WordRAM.ThreeSum.Cell
