/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Collisions
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Native Chan–He collision counting

This fixed native program first decodes signed Euclidean residue keys, then builds a
histogram and counts ordered collisions. Register setup between the two loops is charged.
For injective input arrays its counter is exactly the existing Chan–He `coll`.

## Main definitions

* `Count.program`: the composed native residue/histogram program.
* `Count.memory`: the complete output memory, including the residue scratch array.

## Main results

* `Count.exec`: execution in at most `34n + 5M + 18` native instructions.
* `Count.exec_coll`: the counter equals the existing mathematical collision count.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Count

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Residue routine registers occupy the first sixteen registers. -/
def residuesRegisters (i : Fin 16) : Fin 28 := ⟨i.val, by omega⟩

/-- Histogram registers occupy registers sixteen through twenty-six. -/
def histogramRegisters (i : Fin 11) : Fin 28 := ⟨16 + i.val, by omega⟩

private theorem residues_injective : Function.Injective residuesRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 28 => i.val) h

private theorem histogram_injective : Function.Injective histogramRegisters := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [histogramRegisters] at this
  omega

/-- Encoded integer input base. -/
abbrev src : Fin 28 := 9
/-- Residue scratch base. -/
abbrev scratch : Fin 28 := 10
/-- Number of input values. -/
abbrev len : Fin 28 := 11
/-- Encoded positive modulus. -/
abbrev modulus : Fin 28 := 12
/-- Histogram destination base. -/
abbrev dst : Fin 28 := 27
/-- Output collision count, an ordinary unsigned word. -/
abbrev total : Fin 28 := 24

/-- Histogram input base register. -/
abbrev hsrc : Fin 28 := histogramRegisters Histogram.src
/-- Histogram output base register. -/
abbrev hdst : Fin 28 := histogramRegisters Histogram.dst
/-- Histogram length register. -/
abbrev hlen : Fin 28 := histogramRegisters Histogram.len
/-- Histogram modulus register. -/
abbrev hbins : Fin 28 := histogramRegisters Histogram.bins
/-- Histogram constant register, also used to decode the encoded modulus. -/
abbrev hone : Fin 28 := histogramRegisters Histogram.one

/-- Set up the histogram parameters, explicitly decoding the positive modulus. -/
def prepare : Code .standard 28 := ram[
  hsrc ← scratch; hdst ← dst; hlen ← len; hone ← #2; hbins ← modulus / hone ]

/-- A single finite native program, independent of input length, modulus and word width. -/
def program : Code .standard 28 :=
  .seq (Residues.program.rename residuesRegisters)
    (.seq prepare (Histogram.program.rename histogramRegisters))

/-- The complete counting program preserves its input base, scratch base, length,
encoded modulus and histogram base registers. -/
theorem preserves_parameters (i : Fin 28)
    (hi : (9 ≤ i.val ∧ i.val ≤ 12) ∨ i = dst) : program.Preserves i := by
  fin_cases i <;> norm_num [dst] at hi <;> decide

/-- The residue scratch array and the complete histogram, framed by the original memory. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M scratch dst : ℕ) : ℕ → ℕ :=
  Histogram.memory (Residues.memory mem values M scratch n)
    (fun i => (values i % (M : ℤ)).toNat) dst M n

/-- Complete native collision counting, including residue computation, clearing the histogram
and register setup. Input, scratch and histogram blocks occur in that order and are disjoint.
The final halt is excluded. Fit hypotheses are local; a caller must derive them from its
input and width contract. -/
theorem exec {w M : ℕ} (x : Data 28) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs src + x.regs len))
    (hk : Fits (w + 2) (x.regs scratch + x.regs len))
    (hd : Fits (w + 2) (x.regs dst + M))
    (ht : Fits (w + 2) (x.regs len * x.regs len + x.regs len + 1))
    (hsk : x.regs src + x.regs len ≤ x.regs scratch)
    (hkd : x.regs scratch + x.regs len ≤ x.regs dst)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i)) :
    ∃ y, ExecWithin (w + 2) program x y (34 * x.regs len + 5 * M + 18) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs scratch) (x.regs dst) ∧
      y.regs total = Histogram.pairs (fun i => (values i % (M : ℤ)).toNat) (x.regs len) ∧
      ∀ i, ((9 ≤ i.val ∧ i.val ≤ 12) ∨ i = dst) → y.regs i = x.regs i := by
  obtain ⟨a, ha, ham, har⟩ := Residues.exec (x.comap residuesRegisters) values hM hmod
    hmodreg hfit hs hk hsk hinput
  let y := a.extend residuesRegisters x
  have hy : ExecWithin (w + 2) (Residues.program.rename residuesRegisters) x y
      (23 * x.regs len + 4) := ha.rename residues_injective
  have hyr (i : Fin 16) : y.regs (residuesRegisters i) = a.regs i :=
    residues_injective.extend_apply _ _ i
  have hys : y.regs scratch = x.regs scratch :=
    (hyr Residues.dst).trans (har Residues.dst (by decide))
  have hyl : y.regs len = x.regs len := (hyr Residues.len).trans (har Residues.len (by decide))
  have hym : y.regs modulus = encode (M : ℤ) :=
    (hyr Residues.modulus).trans ((har Residues.modulus (by decide)).trans hmodreg)
  have hyd : y.regs dst = x.regs dst := by
    change Function.extend residuesRegisters a.regs x.regs dst = x.regs dst
    apply Function.extend_apply'
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    dsimp [residuesRegisters, dst] at this
    omega
  let q := ((((y.set (histogramRegisters Histogram.src) (x.regs scratch)).set
      (histogramRegisters Histogram.dst) (x.regs dst)).set
      (histogramRegisters Histogram.len) (x.regs len)).set
      (histogramRegisters Histogram.one) 2).set (histogramRegisters Histogram.bins) M
  have htwo : Fits (w + 2) 2 := (show Fits 2 2 from by decide).mono (by omega)
  have hraw : Fits (w + 2) M :=
    ((encode_fits hmod).mono (by omega)).of_le (by
      simp only [encode, Int.natAbs_natCast]
      omega)
  have hprep : ExecWithin (w + 2) prepare y q 5 := by
    ram_eval [prepare, q, hys, hyl, hym, hyd, htwo, hraw, histogramRegisters,
      Histogram.src, Histogram.dst, Histogram.len, Histogram.one, Histogram.bins,
      hsrc, hdst, hlen, hbins, hone, scratch, len, modulus, dst, Fin.mk.injEq,
      encode_div_two, Int.natAbs_natCast]
  have hqs : (q.comap histogramRegisters).regs Histogram.src = x.regs scratch := by
    simp +decide [q, histogramRegisters, Histogram.src, Histogram.dst, Histogram.len,
      Histogram.one, Histogram.bins]
  have hqd : (q.comap histogramRegisters).regs Histogram.dst = x.regs dst := by
    simp +decide [q, histogramRegisters, Histogram.src, Histogram.dst, Histogram.len,
      Histogram.one, Histogram.bins]
  have hql : (q.comap histogramRegisters).regs Histogram.len = x.regs len := by
    simp +decide [q, histogramRegisters, Histogram.src, Histogram.dst, Histogram.len,
      Histogram.one, Histogram.bins]
  have hqb : (q.comap histogramRegisters).regs Histogram.bins = M := by
    simp [q]
  have hqm : q.mem = Residues.memory x.mem values M (x.regs scratch) (x.regs len) := ham
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  obtain ⟨b, hb, hbm, hbt, _⟩ := Histogram.exec (q.comap histogramRegisters)
    (fun i => (values i % (M : ℤ)).toNat) h1
    (by simpa only [hqs, hql] using hk) (by simpa only [hqd, hqb] using hd)
    (by simpa only [hql] using ht) (by simpa only [hqs, hql, hqd] using hkd)
    (by
      intro i hi
      rw [hqb]
      have hnonneg := Int.emod_nonneg (values i) (show (M : ℤ) ≠ 0 by omega)
      have hlt := Int.emod_lt_of_pos (values i) (show (0 : ℤ) < M by omega)
      omega)
    (by
      intro i hi
      have hi' : i < x.regs len := by simpa only [hql] using hi
      rw [Data.comap_mem, hqm, hqs]
      simp [Residues.memory, hi'])
  have he := (hy.seq (hprep.seq (hb.rename histogram_injective))).mono
    (show (23 * x.regs len + 4) + (5 + (5 * (q.comap histogramRegisters).regs Histogram.bins +
      11 * (q.comap histogramRegisters).regs Histogram.len + 9)) ≤
        34 * x.regs len + 5 * M + 18 by rw [hql, hqb]; omega)
  refine ⟨b.extend histogramRegisters q, he, ?_, ?_, fun i hi =>
    ExecWithin.regs_eq he (preserves_parameters i hi)⟩
  · change b.mem = _
    rw [hbm, Data.comap_mem, hqm, hqd, hqb, hql]
    rfl
  · change Function.extend histogramRegisters b.regs q.regs
      (histogramRegisters Histogram.total) = _
    rw [histogram_injective.extend_apply, hbt, hql]

/-- For an injective integer array, the composed program returns exactly the collision
count used by the existing Chan–He prime searches. -/
theorem exec_coll {w M : ℕ} (x : Data 28) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs src + x.regs len))
    (hk : Fits (w + 2) (x.regs scratch + x.regs len))
    (hd : Fits (w + 2) (x.regs dst + M))
    (ht : Fits (w + 2) (x.regs len * x.regs len + x.regs len + 1))
    (hsk : x.regs src + x.regs len ≤ x.regs scratch)
    (hkd : x.regs scratch + x.regs len ≤ x.regs dst)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i))
    (hinj : Set.InjOn values (↑(Finset.range (x.regs len)) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y (34 * x.regs len + 5 * M + 18) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs scratch) (x.regs dst) ∧
      y.regs total = Cslib.Algorithms.ThreeSum.ChanHe.coll
        ((Finset.range (x.regs len)).image values) M ∧
      ∀ i, ((9 ≤ i.val ∧ i.val ≤ 12) ∨ i = dst) → y.regs i = x.regs i := by
  obtain ⟨y, hy, hm, ht, hr⟩ := exec x values hM hmod hmodreg hfit hs hk hd ht hsk hkd hinput
  exact ⟨y, hy, hm, ht.trans (coll_eq_histogramPairs values _ M hM hinj).symm, hr⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Count
