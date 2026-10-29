/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PlaceExec
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PlaceMemory

/-!
# A complete native counting and placement call

This routine actually computes the residues and histogram before extracting a heavy array and
placing the corresponding packed column. The histogram is not a premise of the execution
contract. It also writes the compact output count to its caller-supplied descriptor cell.

## Main definitions

* `CountPlace.program`: modulus encoding, complete `CountCall.program 2`, runtime argument
  delivery, complete `Place.program`, and the count store.

## References

This native composition is original and reuses the existing Chan–He mathematical definitions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Input length (the selected third argument of the existing counting call). -/
abbrev len : Fin 64 := 32
/-- Signed input base. -/
abbrev src : Fin 64 := 33
/-- Unsigned residue workspace base. -/
abbrev scratch : Fin 64 := 34
/-- Histogram workspace base. -/
abbrev hist : Fin 64 := 35
/-- Compact heavy output base. -/
abbrev heavy : Fin 64 := 37
/-- Packed node array base. -/
abbrev packed : Fin 64 := 38
/-- Positive modulus, decoded unsigned. -/
abbrev modulus : Fin 64 := 40
/-- Encoded positive tag. -/
abbrev tag : Fin 64 := 41
/-- Packed column. -/
abbrev column : Fin 64 := 42
/-- Distance between the two stores. -/
abbrev distance : Fin 64 := 43
/-- Zero for X/Y, one for Z. -/
abbrev negative : Fin 64 := 44
/-- Cell in which the exact heavy count is stored. -/
abbrev descriptor : Fin 64 := 45

/-- Fixed embedding of the placement workspace below all caller parameters. -/
def registers (i : Fin 32) : Fin 64 := ⟨i.val, by omega⟩

private theorem registers_injective : Function.Injective registers := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 64 => k.val) he

@[inherit_doc Place.src]
abbrev psrc : Fin 64 := registers Place.src
@[inherit_doc Place.keys]
abbrev pkeys : Fin 64 := registers Place.keys
@[inherit_doc Place.len]
abbrev plen : Fin 64 := registers Place.len
@[inherit_doc Place.hist]
abbrev phist : Fin 64 := registers Place.hist
@[inherit_doc Place.heavy]
abbrev pheavy : Fin 64 := registers Place.heavy
@[inherit_doc Place.packed]
abbrev ppacked : Fin 64 := registers Place.packed
@[inherit_doc Place.modulus]
abbrev pmodulus : Fin 64 := registers Place.modulus
@[inherit_doc Place.tag]
abbrev ptag : Fin 64 := registers Place.tag
@[inherit_doc Place.column]
abbrev pcolumn : Fin 64 := registers Place.column
@[inherit_doc Place.distance]
abbrev pdistance : Fin 64 := registers Place.distance
@[inherit_doc Place.negative]
abbrev pnegative : Fin 64 := registers Place.negative
@[inherit_doc Place.count]
abbrev pcount : Fin 64 := registers Place.count

/-- All eleven runtime argument copies are real instructions. -/
def prepare : Code .standard 64 := ram[
  psrc ← src; pkeys ← scratch; plen ← len; phist ← hist; pheavy ← heavy;
  ppacked ← packed; pmodulus ← modulus; ptag ← tag; pcolumn ← column;
  pdistance ← distance; pnegative ← negative ]

/-- Complete fixed native routine: no host histogram, heavy filter or output constructor. -/
def program : Code .standard 64 :=
  .seq (.op (.bin .add CountCall.modulus modulus modulus))
    (.seq (CountCall.program 2) (.seq prepare
      (.seq (Place.program.rename registers) (.op (.store descriptor pcount)))))

/-- Only the counting/placement workspace, the encoded modulus, and the discarded collision
counter can change. All caller registers at least 46 are included in this frame. -/
theorem preserves (i : Fin 64) (hi : 32 ≤ i.val) (hm : i ≠ CountCall.modulus)
    (hc : i ≠ CountCall.result 2) : program.Preserves i := by
  have h : 32 ≤ i.val ∧ i ≠ CountCall.modulus ∧ i ≠ CountCall.result 2 := ⟨hi, hm, hc⟩
  fin_cases i <;> norm_num [CountCall.modulus, CountCall.result] at h <;> decide

/-- Polynomial envelope for addresses, counters, encoded magnitudes and every scan intermediate. -/
def budget (x : Data 64) (M N U t : ℕ) : ℕ :=
  x.regs src + x.regs scratch + x.regs hist + x.regs heavy + x.regs packed +
    x.regs len * x.regs len + 2 * x.regs len + M + 4 * N + 2 * t + 2 * U + 64

/-- Exact memory, including actual residue/histogram construction and the descriptor write. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col dist t scratch hist descriptor : ℕ) (neg : Bool) : ℕ → ℕ :=
  Function.update
    (Place.memory (Count.memory mem values n M scratch hist) values n M out dst col dist t neg n)
    descriptor (Place.heavyList values n M n).length

/-- Complete native count/extract/place execution, charging modulus encoding, all subroutine
argument/result copies and the final count write. The caller supplies actual signed input words;
no histogram or light/heavy-output contract is assumed. -/
theorem exec {w M N U t : ℕ} (x : Data 64) (values : ℕ → ℤ) (neg : Bool)
    (hM : 0 < M) (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmreg : x.regs modulus = M) (hN : 2 * M ≤ N) (ht : U ≤ t)
    (htag : x.regs tag = 2 * t) (hneg : x.regs negative = if neg then 1 else 0)
    (hc : x.regs column < 4) (hd : x.regs distance ≤ 4 * M)
    (hbdd : ∀ i < x.regs len, (values i).natAbs ≤ U)
    (hsigned : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hfit : Fits (w + 2) (budget x M N U t))
    (hsh : x.regs src + x.regs len ≤ x.regs heavy)
    (hhp : x.regs heavy + x.regs len ≤ x.regs packed)
    (hpk : x.regs packed + 4 * N ≤ x.regs scratch)
    (hkh : x.regs scratch + x.regs len ≤ x.regs hist)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i))
    (hinj : Set.InjOn values (↑(Finset.range (x.regs len)) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y (66 * x.regs len + 5 * M + 45) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t (x.regs scratch) (x.regs hist)
        (x.regs descriptor) neg ∧
      ∀ i, 32 ≤ i.val → i ≠ CountCall.modulus → i ≠ CountCall.result 2 →
        y.regs i = x.regs i := by
  let z := x.set CountCall.modulus (encode (M : ℤ))
  have hemod : encode (M : ℤ) = M + M := by simp [encode, two_mul]
  have hz : ExecWithin (w + 2) (.op (.bin .add CountCall.modulus modulus modulus)) x z 1 := by
    have hf : Fits (w + 2) (x.regs modulus + x.regs modulus) := by
      rw [hmreg, ← hemod]
      exact (encode_fits hmod).mono (by omega)
    simpa only [BinOp.eval, hmreg, ← hemod] using
      (ExecWithin.bin (d := CountCall.modulus) (f := .add) (i := modulus) (j := modulus) hf)
  have zmem : z.mem = x.mem := rfl
  have zreg (i : Fin 64) (hi : i ≠ CountCall.modulus) : z.regs i = x.regs i := by
    simp only [z, Data.set_regs, Function.update_of_ne hi]
  have fs : Fits (w + 2) (x.regs src + x.regs len) := hfit.of_le (by
    dsimp only [budget]; omega)
  have fk : Fits (w + 2) (x.regs scratch + x.regs len) := hfit.of_le (by
    dsimp only [budget]; omega)
  have fh : Fits (w + 2) (x.regs hist + M) := hfit.of_le (by dsimp only [budget]; omega)
  have fn : Fits (w + 2) (x.regs len * x.regs len + x.regs len + 1) :=
    hfit.of_le (by dsimp only [budget]; omega)
  have zlen : z.regs (CountCall.length 2) = x.regs len := zreg _ (by decide)
  have zsrc : z.regs (CountCall.source 2) = x.regs src := zreg _ (by decide)
  have zscratch : z.regs CountCall.scratch = x.regs scratch := zreg _ (by decide)
  have zhist : z.regs CountCall.histogram = x.regs hist := zreg _ (by decide)
  obtain ⟨a, ha, ham, _, har⟩ := CountCall.exec 2 z values hM hmod
    (by simp [z]) (by simpa only [zlen] using hsigned)
    (by simpa only [zsrc, zlen] using fs) (by simpa only [zscratch, zlen] using fk)
    (by simpa only [zhist] using fh) (by simpa only [zlen] using fn)
    (by rw [zsrc, zlen, zscratch]; omega)
    (by simpa only [zscratch, zlen, zhist] using hkh)
    (by simpa only [zsrc, zlen, zmem] using hinput)
    (by simpa only [zlen] using hinj)
  have ar (i : Fin 64) (hi : 32 ≤ i.val) (hm : i ≠ CountCall.modulus)
      (hc : i ≠ CountCall.result 2) : a.regs i = x.regs i :=
    (har i (by omega) hc).trans (zreg i hm)
  have am : a.mem = Count.memory x.mem values (x.regs len) M
      (x.regs scratch) (x.regs hist) := by
    simpa only [zlen, zscratch, zhist, zmem] using ham
  let q := ((((((((((a.set psrc (x.regs src)).set pkeys (x.regs scratch)).set plen
    (x.regs len)).set phist (x.regs hist)).set pheavy (x.regs heavy)).set ppacked
    (x.regs packed)).set pmodulus (x.regs modulus)).set ptag (x.regs tag)).set pcolumn
    (x.regs column)).set pdistance (x.regs distance)).set pnegative (x.regs negative)
  have hp : ExecWithin (w + 2) prepare a q 11 := by
    have rsrc := ar src (by decide) (by decide) (by decide)
    have rlen := ar len (by decide) (by decide) (by decide)
    have rk := ar scratch (by decide) (by decide) (by decide)
    have rh := ar hist (by decide) (by decide) (by decide)
    have ro := ar heavy (by decide) (by decide) (by decide)
    have rp := ar packed (by decide) (by decide) (by decide)
    have rm := ar modulus (by decide) (by decide) (by decide)
    have rt := ar tag (by decide) (by decide) (by decide)
    have rc := ar column (by decide) (by decide) (by decide)
    have rd := ar distance (by decide) (by decide) (by decide)
    have rn := ar negative (by decide) (by decide) (by decide)
    ram_eval [prepare, q, rsrc, rlen, rk, rh, ro, rp, rm, rt, rc, rd, rn]
  have qs : (q.comap registers).regs Place.src = x.regs src := by
    simp +decide [q, registers, Place.src]
  have qk : (q.comap registers).regs Place.keys = x.regs scratch := by
    simp +decide [q, registers, Place.keys]
  have qn : (q.comap registers).regs Place.len = x.regs len := by
    simp +decide [q, registers, Place.len]
  have qh : (q.comap registers).regs Place.hist = x.regs hist := by
    simp +decide [q, registers, Place.hist]
  have qo : (q.comap registers).regs Place.heavy = x.regs heavy := by
    simp +decide [q, registers, Place.heavy]
  have qp : (q.comap registers).regs Place.packed = x.regs packed := by
    simp +decide [q, registers, Place.packed]
  have qm : (q.comap registers).regs Place.modulus = x.regs modulus := by
    simp +decide [q, registers, Place.modulus]
  have qt : (q.comap registers).regs Place.tag = x.regs tag := by
    simp +decide [q, registers, Place.tag]
  have qc : (q.comap registers).regs Place.column = x.regs column := by
    simp +decide [q, registers, Place.column]
  have qd : (q.comap registers).regs Place.distance = x.regs distance := by
    simp +decide [q, registers, Place.distance]
  have qg : (q.comap registers).regs Place.negative = x.regs negative := by
    simp +decide [q, registers, Place.negative]
  have qmem : q.mem = a.mem := rfl
  have qfit : Fits (w + 2) (Place.budget (q.comap registers) M N U t) := by
    rw [Place.budget, qs, qk, qh, qo, qp, qn]
    exact hfit.of_le (by dsimp only [budget]; omega)
  obtain ⟨b, hb, hbm, hbc, _⟩ := Place.exec (q.comap registers) values neg hM hN
    (by simpa only [qc] using hc) (by simpa only [qd] using hd) ht
    (qm.trans hmreg) (qt.trans htag) (qg.trans hneg)
    (by simpa only [qn] using hbdd) qfit
    (by simpa only [qs, qn, qo] using hsh) (by simpa only [qo, qn, qp] using hhp)
    (by simpa only [qp, qk] using hpk) (by simpa only [qk, qn, qh] using hkh)
    (by
      intro i hi
      rw [Data.comap_mem, qmem, am, qs]
      have hi' : i < x.regs len := by simpa only [qn] using hi
      rw [Count.memory_before _ _ _ _ _ _ _ (by omega) (by omega)]
      exact hinput i hi')
    (by
      intro i hi
      have hi' : i < x.regs len := by simpa only [qn] using hi
      rw [Data.comap_mem, qmem, am, qk, Count.memory, Histogram.memory,
        ite_eq_right (by omega)]
      simp [Residues.memory, show i < x.regs len by simpa only [qn] using hi, residueKey])
    (by
      intro r hr
      rw [Data.comap_mem, qmem, am, qh, Count.memory, Histogram.memory_read _ _ _ _ _ _ hr]
      rfl)
  let y := b.extend registers q
  have hy : ExecWithin (w + 2) (Place.program.rename registers) q y
      (32 * x.regs len + 8) := by simpa only [qn] using hb.rename registers_injective
  have yc : y.regs pcount = (Place.heavyList values (x.regs len) M (x.regs len)).length := by
    change Function.extend registers b.regs q.regs (registers Place.count) = _
    rw [registers_injective.extend_apply, hbc, qn]
  have yd : y.regs descriptor = x.regs descriptor := by
    change Function.extend registers b.regs q.regs descriptor = _
    rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      dsimp only [registers, descriptor] at this
      omega)]
    have hq : q.regs descriptor = a.regs descriptor := by simp +decide [q, descriptor]
    exact hq.trans (ar descriptor (by decide) (by decide) (by decide))
  have ha' : ExecWithin (w + 2) (CountCall.program 2) z a
      (34 * x.regs len + 5 * M + 24) := by simpa only [zlen] using ha
  have he := hz.seq (ha'.seq
    (hp.seq (hy.seq (ExecWithin.store (a := descriptor) (s := pcount)))))
  refine ⟨y.write (y.regs descriptor) (y.regs pcount), he.mono (by omega), ?_, ?_⟩
  · simp only [Data.write_mem, yd, yc]
    change Function.update b.mem (x.regs descriptor) _ = _
    rw [hbm, Data.comap_mem, qmem, am, qn, qo, qp, qc, qd]
    rfl
  · intro i hi hm hc
    exact ExecWithin.regs_eq he (preserves i hi hm hc)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace
