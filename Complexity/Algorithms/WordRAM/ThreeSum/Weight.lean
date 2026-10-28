/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.Convolution
public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Native weight selection for the Convolution-3SUM reduction

Directly adapts `pickStmt` and `putStmt` of Anthropic's [pinned graph builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Fill.lean).
This code uses the existing unsigned word RAM,
its sign-and-magnitude encoding, and its proved subtraction block. No source machine is copied.

One input register holds a signed index, which may be negative or out of range. The code reads
only when the index is nonnegative and below `N`; otherwise it uses the filler. It optionally
negates the selected value and stores it at a supplied destination. Addresses and lengths are
unsigned; index, filler and input values are encoded signed integers. The nine arithmetic
registers are scratch, and the five argument registers are preserved. Destination/input overlap
is allowed for this single read-then-write operation; graph-building loops need their own frame.

The theorem charges selection, optional negation and the store, excluding a final halt.
`Exec.executes` adds one instruction for that halt. Computing the index, arranging
arguments, traversing matrices and invoking Exact Triangle are not included. This is a graph
construction kernel, not a complete reduction or a subquadratic 3SUM solver.

## Main definitions

* `Weight.select`: guarded read, falling back to the encoded filler.
* `Weight.store`: select, optionally negate, and store one graph weight.

## Main results

* `Weight.exec_store`: at most twenty-eight native instructions at width `w + 2`.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Weight

open Cslib.WordRAM
open Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum (pick)

/-- Encoded signed index to read. -/
abbrev index : Fin 14 := ⟨9, by decide⟩
/-- Unsigned input length. -/
abbrev len : Fin 14 := ⟨10, by decide⟩
/-- Unsigned input base address. -/
abbrev base : Fin 14 := ⟨11, by decide⟩
/-- Encoded fallback value. -/
abbrev filler : Fin 14 := ⟨12, by decide⟩
/-- Unsigned destination address. -/
abbrev dest : Fin 14 := ⟨13, by decide⟩

/-- Select a signed input word into `right`, rejecting negative indices before any load. -/
def select : Code .standard 14 := ram[
  two ← #2; zero ← #0; magA ← index / two; signA ← index % two;
  right ← filler;
  if signA = zero then [
    if magA < len then [ magA ← base + magA; right ← *magA ]
    else [ right ← right ] ] else [ right ← right ] ]

/-- Store a selected weight, optionally negated; all five argument registers are preserved. -/
def store (negate : Bool) : Code .standard 14 :=
  .seq (.seq select (.op (.const left 0)))
    (.seq (if negate then subtract else .op (.copy result right)) (.op (.store dest result)))

private def selected (x : Data 14) (z : ℤ) (N b : ℕ) : Data 14 :=
  let y := ((((x.set two 2).set zero 0).set magA z.natAbs).set signA
    (if z < 0 then 1 else 0)).set right (x.regs filler)
  if 0 ≤ z ∧ z < N then
    (y.set magA (b + z.toNat)).set right (x.mem (b + z.toNat)) else y

private theorem exec_select {w N b : ℕ} {μ : ℕ → ℤ} {fill z : ℤ} (x : Data 14)
    (hindex : x.regs index = encode z) (hlen : x.regs len = N)
    (hbase : x.regs base = b) (hfiller : x.regs filler = encode fill)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hz : GenericRAM.Signed.Fits w z) (haddr : Fits (w + 2) (b + N)) :
    ExecWithin (w + 2) select x (selected x z N b) 9 ∧
      (selected x z N b).regs right = encode (pick N μ fill z) ∧
      (selected x z N b).mem = x.mem := by
  have h2 : Fits (w + 2) 2 := (show Fits 2 2 from by decide).mono (by omega)
  have h1 : Fits (w + 2) 1 := h2.of_le (by decide)
  have hmag : Fits (w + 2) z.natAbs :=
    ((encode_fits hz).mono (by omega)).of_le (by unfold encode; split_ifs <;> omega)
  by_cases hn : z < 0
  · refine ⟨?_, ?_, by dsimp only [selected]; split_ifs <;> rfl⟩
    · have hnonneg : ¬0 ≤ z := by omega
      simp only [selected, hnonneg, false_and, ↓reduceIte]
      ram_eval [select, hn, hindex, hlen, hbase, hfiller,
        encode_div_two, encode_mod_two, h2, h1, hmag, left, right, two, zero, magA, signA,
        index, len, base, filler, Fin.mk.injEq, WordRAM.Data.set, Function.update_idem]
    · simp [selected, pick, hn, show ¬0 ≤ z by omega, hfiller]
  · have hnonneg : 0 ≤ z := by omega
    have habs : z.natAbs = z.toNat := by omega
    have hmagNat : Fits (w + 2) z.toNat := by simpa only [habs] using hmag
    by_cases hi : z < N
    · have hfit : Fits (w + 2) (b + z.toNat) := haddr.of_le (by omega)
      refine ⟨?_, ?_, by dsimp only [selected]; split_ifs <;> rfl⟩
      · simp only [selected, hnonneg, hi, true_and, ↓reduceIte]
        ram_eval [select, hn, hnonneg, hi, hindex, hlen, hbase, hfiller,
          encode_div_two, encode_mod_two, h2, h1, hmagNat, hfit, habs,
          show z.toNat < N by omega, left, right, two, zero, magA, signA,
          index, len, base, filler, Fin.mk.injEq, WordRAM.Data.set, Function.update_idem]
      · simp [selected, pick, hnonneg, hi, hmem z.toNat (by omega)]
    · refine ⟨?_, ?_, by dsimp only [selected]; split_ifs <;> rfl⟩
      · simp only [selected, hnonneg, hi, true_and, ↓reduceIte]
        ram_eval [select, hn, hnonneg, hi, hindex, hlen, hbase, hfiller,
          encode_div_two, encode_mod_two, h2, h1, hmagNat, habs,
          show ¬z.toNat < N by omega, left, right, two, zero, magA, signA,
          index, len, base, filler, Fin.mk.injEq, WordRAM.Data.set, Function.update_idem]
      · simp [selected, pick, hnonneg, hi, hfiller]

/-- A selected signed weight is stored within twenty-eight unsigned instructions. All address
arithmetic is charged, but computing the signed index and preparing arguments are caller costs.
The signed bounds are satisfiable even for negative, zero and out-of-range indices. -/
theorem exec_store {w N b d : ℕ} {μ : ℕ → ℤ} {fill z : ℤ} (negate : Bool) (x : Data 14)
    (hindex : x.regs index = encode z) (hlen : x.regs len = N)
    (hbase : x.regs base = b) (hfiller : x.regs filler = encode fill)
    (hdest : x.regs dest = d) (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hz : GenericRAM.Signed.Fits w z) (hfill : GenericRAM.Signed.Fits w fill)
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i)) (haddr : Fits (w + 2) (b + N)) :
    ∃ y, ExecWithin (w + 2) (store negate) x y 28 ∧
      y.mem = Function.update x.mem d
        (encode (if negate then -pick N μ fill z else pick N μ fill z)) ∧
      ∀ i : Fin 14, 9 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨hs, hv, hm⟩ := exec_select x hindex hlen hbase hfiller hmem hz haddr
  let q := (selected x z N b).set left 0
  have hq : q.regs right = encode (pick N μ fill z) := by simpa [q, right, left] using hv
  have hqr : q.regs left = encode 0 := by simp [q, encode]
  have hval : GenericRAM.Signed.Fits w (pick N μ fill z) := by
    unfold pick
    split_ifs with h
    · exact hμ _ (by omega)
    · exact hfill
  have hpre : ExecWithin (w + 2) (.seq select (.op (.const left 0))) x q 10 :=
    hs.seq (Exec.const (fits_zero (w + 2))).within
  have hpres : ∀ i : Fin 14, 9 ≤ i.val → (store negate).Preserves i := by
    intro i hi
    cases negate <;> simp only [store, Bool.false_eq_true, ↓reduceIte] <;>
      simp only [not_false_eq_true, and_true, reduceCtorEq, select, subtract, unpack,
        flipRightSign, addCore, addMagnitudes, finish,
        Code.Preserves, Op.bin, Op.dest, ne_eq, Option.some.injEq, left, right, result, two,
        zero, magA, magB, signA, signB, index, len, base, filler, Fin.ext_iff] <;> omega
  have hqd : q.regs dest = d := (hpre.regs_eq (by decide)).trans hdest
  cases negate with
  | false =>
    have hc : Exec (B := .standard) (w + 2) (.op (.copy result right)) q
        (q.set result (encode (pick N μ fill z))) 1 := by
      simpa only [hq] using
        (Exec.copy (B := .standard) (w := w + 2) (x := q) (d := result) (s := right))
    have hd : (q.set result (encode (pick N μ fill z))).regs dest = d := by
      simpa [result, dest, Fin.mk.injEq] using hqd
    have he := (hpre.seq (hc.within.seq (Exec.store (B := .standard) (w := w + 2)
      (x := q.set result (encode (pick N μ fill z))) (a := dest) (s := result)).within)).mono
      (by decide : 10 + (1 + 1) ≤ 28)
    refine ⟨_, by simpa only [store, Bool.false_eq_true, ↓reduceIte] using he, ?_,
      fun i hi => he.regs_eq (by
        simpa only [store, Bool.false_eq_true, ↓reduceIte] using hpres i hi)⟩
    simp only [WordRAM.Data.write_mem, hd, WordRAM.Data.set_regs, Function.update_self,
      WordRAM.Data.set_mem, q, hm, Bool.false_eq_true, ↓reduceIte]
  | true =>
    obtain ⟨y, hy, hyr, hym, hyreg⟩ := exec_subtract (GenericRAM.Signed.fits_zero hz.1)
      hval q hqr hq
    have hyd : y.regs dest = d := (hyreg dest (Or.inr (by decide))).trans hqd
    have hlast := (Exec.store (B := .standard) (w := w + 2) (x := y)
      (a := dest) (s := result)).within
    have he := hpre.seq (hy.seq hlast)
    refine ⟨_, by simpa only [store, ↓reduceIte] using he, ?_,
      fun i hi => he.regs_eq (by simpa only [store, ↓reduceIte] using hpres i hi)⟩
    simp [WordRAM.Data.write, hyr, hyd, GenericRAM.Signed.Arithmetic.eval,
      hym, q, hm]

end Cslib.Algorithms.WordRAM.ThreeSum.Weight
