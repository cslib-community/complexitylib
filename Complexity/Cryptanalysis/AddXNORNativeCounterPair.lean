/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeClassCounters
public import Complexity.Computability.WordRAM.RegisterFrame
import all Complexity.Cryptanalysis.AddXNORNativeClassCounters
import all Complexity.Cryptanalysis.AddXNORNativeBalance

/-!
# Native paired counters and computed balance

Both counter arrays are constructed from original arrays before the native
maximum-of-minima scan. The preserved high register bank holds the actual result
pointers and computed balance; no class size or balance is supplied as input.
The backward input is the reversed suffix, seeded at the complemented target.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- Private subroutines use the lower thirty-two registers. -/
abbrev bank (i : Fin 32) : Fin 40 := i.castLE (by decide)

/-- Injectivity of the physical register-bank inclusion. -/
theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Fin 40 => r.val) h)

/-- Actual output counter pointers, computed balance and orientation flag. -/
abbrev forwardPointer : Fin 40 := 32
/-- Preserved pointer to the actual backward counter result. -/
abbrev backwardPointer : Fin 40 := 33
/-- Maximum of minima computed before class retention. -/
abbrev balance : Fin 40 := 34
/-- Returned direction bit: one denotes conjugated inverse retention. -/
abbrev orientation : Fin 40 := 35
/-- A preserved zero for outer control. -/
abbrev zero : Fin 40 := 38

/-- Counter kernel bank inside the outer register file. -/
abbrev counterBank (i : Fin 18) : Fin 40 := bank (counterRegs i)

private theorem counterBank_injective : Function.Injective counterBank := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Fin 40 => r.val) h)

/-- Addresses of the embedded counter registers. -/
abbrev counterSource := counterBank source
/-- Destination-buffer register in the embedded counter bank. -/
abbrev counterDestination := counterBank destination
/-- Projection modulus register in the embedded counter bank. -/
abbrev counterModulus := counterBank Native.modulus
/-- Balance-scan answer register in the embedded counter bank. -/
abbrev counterAnswer := counterBank answer

/-- Construct both multiplicity-preserving tables from full-width operands. -/
@[expose] def countPair (a n b k q B r C N s t : ℕ) : Code .standard 40 :=
  .seq ((countHalf a q B n N s).rename bank)
    (.seq (ram[ forwardPointer ← counterSource ])
      (.seq ((countHalf b r C k N t).rename bank)
        (ram[ backwardPointer ← counterSource ])))

/-- Read the two native result pointers and scan the actual arrays. -/
@[expose] def computeBalance (N : ℕ) : Code .standard 40 :=
  .seq (ram[ counterSource ← forwardPointer;
    counterDestination ← backwardPointer; counterModulus ← #N ])
    (.seq (Balance.scan.rename counterBank)
      (ram[ balance ← counterAnswer; zero ← #0 ]))

/-- Counter construction and balance computation precede every retained class. -/
@[expose] def prepare (a n b k q B r C N s t : ℕ) : Code .standard 40 :=
  .seq (countPair a n b k q B r C N s t) (computeBalance N)

/-- Actual two-table construction with a memory frame. This component accepts
raw operand arrays and physical capacity only, never correct counter contents. -/
theorem countPair_exec {W m p a b q B r C : ℕ} (as bs : List (BitVec m))
    (s t : BitVec m) (x : Data 40)
    (ha : ∀ i (hi : i < as.length), x.mem (a + i) = as[i].toNat)
    (hb : ∀ i (hi : i < bs.length), x.mem (b + i) = bs[i].toNat)
    (haq : a + as.length ≤ q) (hbq : b + bs.length ≤ q)
    (hqB : q + as.length ≤ B) (hBr : B + 2 * 2 ^ p ≤ r)
    (hrC : r + bs.length ≤ C)
    (hfitF : Fits W (a + q + 2 * B + as.length + 4 * 2 ^ p +
      2 * 2 ^ as.length + 2 ^ m + 12))
    (hfitB : Fits W (b + r + 2 * C + bs.length + 4 * 2 ^ p +
      2 * 2 ^ bs.length + 2 ^ m + 12)) :
    ∃ y, ExecWithin W
        (countPair a as.length b bs.length q B r C (2 ^ p)
          (s.setWidth p).toNat (t.setWidth p).toNat) x y
        (((10 * as.length + 8) + (6 +
          (4 * 2 ^ p + as.length * (14 * 2 ^ p + 14) + 10))) +
          (1 + (((10 * bs.length + 8) + (6 +
            (4 * 2 ^ p + bs.length * (14 * 2 ^ p + 14) + 10))) + 1))) ∧
      Counters.Represents y.mem (y.regs forwardPointer)
        (WordTable.classCounters (as.map (BitVec.setWidth p)) (s.setWidth p)) ∧
      Counters.Represents y.mem (y.regs backwardPointer)
        (WordTable.classCounters (bs.map (BitVec.setWidth p)) (t.setWidth p)) ∧
      (y.regs forwardPointer = B ∨ y.regs forwardPointer = B + 2 ^ p) ∧
      (y.regs backwardPointer = C ∨ y.regs backwardPointer = C + 2 ^ p) ∧
      (∀ z, z < q ∨ C + 2 * 2 ^ p ≤ z → y.mem z = x.mem z) := by
  obtain ⟨u, hu, uf, ub, uframe⟩ := countHalf_exec (p := p) as s (x.comap bank)
    ha haq hqB hfitF
  let u' := u.extend bank x
  have hu' := hu.rename bank_injective
  let v := u'.set forwardPointer (u'.regs (counterSource))
  have hv : ExecWithin (B := .standard) W
      (ram[ forwardPointer ← counterSource ]) u' v 1 := .copy
  obtain ⟨w, hw, wr, wb, wframe⟩ := countHalf_exec (p := p) bs t (v.comap bank)
    (by intro i hi; change u.mem _ = _; rw [uframe _ (Or.inl (by omega))]; exact hb i hi)
    (by omega) hrC hfitB
  let w' := w.extend bank v
  have hw' := hw.rename bank_injective
  let y := w'.set backwardPointer (w'.regs (counterSource))
  have hy : ExecWithin (B := .standard) W
      (ram[ backwardPointer ← counterSource ]) w' y 1 := .copy
  have vp : v.regs forwardPointer = u.regs (counterRegs source) := by
    simp only [v, Data.set_regs, Function.update_self, u', counterSource, counterBank,
      Data.extend, bank_injective.extend_apply]
  have wp : w'.regs forwardPointer = v.regs forwardPointer :=
    hw'.regs_eq (Code.preserves_rename_of_forall_ne _ bank _ (by
      intro j h
      have hv := congrArg (fun r : Fin 40 => r.val) h
      change j.val = 32 at hv
      have hj := j.isLt
      omega))
  have yp : y.regs forwardPointer = u.regs (counterRegs source) :=
    ((hy.regs_eq (by decide)).trans wp).trans vp
  have yr : y.regs backwardPointer = w.regs (counterRegs source) := by
    simp only [y, Data.set_regs, Function.update_self, w', counterSource, counterBank,
      Data.extend, bank_injective.extend_apply]
  refine ⟨y, hu'.seq (hv.seq (hw'.seq hy)), ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [yp]
    change w.mem _ = _
    rw [wframe _ (Or.inl (by
      rcases ub with h | h
      · rw [h]; exact (Nat.add_lt_add_left g.isLt B).trans_le (by omega)
      · rw [h]
        exact (Nat.add_lt_add_left g.isLt (B + 2 ^ p)).trans_le (by omega)))]
    exact uf g
  · intro g; rw [yr]; exact wr g
  · rwa [yp]
  · rwa [yr]
  · intro z hz
    change w.mem z = x.mem z
    rw [wframe z (by omega)]
    exact uframe z (by omega)

/-- Native balance over the actual counter pointers. No array semantics are
needed for execution, and no memory cell is modified. -/
theorem computeBalance_exec {W P Q N : ℕ} (x : Data 40)
    (hp : x.regs forwardPointer = P) (hq : x.regs backwardPointer = Q)
    (hfit : Fits W (P + Q + N + 2)) :
    ∃ y, ExecWithin W (computeBalance N) x y (14 * N + 11) ∧
      y.mem = x.mem ∧ y.regs balance = Balance.prefixMax x.mem P Q N N ∧
      y.regs forwardPointer = P ∧ y.regs backwardPointer = Q ∧ y.regs zero = 0 := by
  let u := x.set counterSource P |>.set counterDestination Q |>.set counterModulus N
  have setup : ExecWithin (B := .standard) W
      (ram[ counterSource ← forwardPointer;
        counterDestination ← backwardPointer; counterModulus ← #N ]) x u 3 := by
    have hn : Fits W N := hfit.of_le (by omega)
    ram_eval [u, hp, hq, hn, counterSource, counterDestination, counterModulus, counterBank,
      bank, counterRegs, source, destination, Native.modulus, forwardPointer, backwardPointer,
      Fin.mk.injEq]
  obtain ⟨v, hv, va, vm, _, _, _⟩ := Balance.scan_exec (u.comap counterBank)
    (by simp +decide [u, counterSource, counterDestination, counterModulus, counterBank,
      bank, counterRegs, source, destination, Native.modulus])
    (by simp +decide [u, counterDestination, counterModulus, counterBank,
      bank, counterRegs, destination, Native.modulus])
    (by simp [u, counterModulus, counterBank]) hfit
  let v' := v.extend counterBank u
  have run := hv.rename counterBank_injective
  let y := v'.set balance (v'.regs counterAnswer) |>.set zero 0
  have done : ExecWithin (B := .standard) W
      (ram[ balance ← counterAnswer; zero ← #0 ]) v' y 2 := by
    ram_eval [y, fits_zero W, balance, zero, Fin.mk.injEq]
  have he : ExecWithin W (computeBalance N) x y (14 * N + 11) :=
    (setup.seq (run.seq done)).mono (by omega)
  refine ⟨y, he, vm, ?_, (he.regs_eq (by
      simp only [computeBalance, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      decide)).trans hp,
    (he.regs_eq (by
      simp only [computeBalance, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      decide)).trans hq, ?_⟩
  · have yb : y.regs balance = v'.regs counterAnswer := by
      simp +decide [y, balance, zero]
    rw [yb]
    change (v.extend counterBank u).regs (counterBank answer) = _
    simpa only [Data.extend, counterBank_injective.extend_apply, u, Data.comap_mem,
      Data.set_mem] using va
  · simp [y]

/-- Original-array construction followed by the actual maximum-of-minima scan.
The final table values and balance are conclusions of this single execution. -/
theorem prepare_exec {W m p a b q B r C : ℕ} (as bs : List (BitVec m))
    (s t : BitVec m) (x : Data 40)
    (ha : ∀ i (hi : i < as.length), x.mem (a + i) = as[i].toNat)
    (hb : ∀ i (hi : i < bs.length), x.mem (b + i) = bs[i].toNat)
    (haq : a + as.length ≤ q) (hbq : b + bs.length ≤ q)
    (hqB : q + as.length ≤ B) (hBr : B + 2 * 2 ^ p ≤ r)
    (hrC : r + bs.length ≤ C)
    (hfitF : Fits W (a + q + 2 * B + as.length + 4 * 2 ^ p +
      2 * 2 ^ as.length + 2 ^ m + 12))
    (hfitB : Fits W (b + r + 2 * C + bs.length + 4 * 2 ^ p +
      2 * 2 ^ bs.length + 2 ^ m + 12))
    (hfitScan : Fits W (B + C + 3 * 2 ^ p + 2)) :
    ∃ y, ExecWithin W
        (prepare a as.length b bs.length q B r C (2 ^ p)
          (s.setWidth p).toNat (t.setWidth p).toNat) x y
        ((((10 * as.length + 8) + (6 +
          (4 * 2 ^ p + as.length * (14 * 2 ^ p + 14) + 10))) +
          (1 + (((10 * bs.length + 8) + (6 +
            (4 * 2 ^ p + bs.length * (14 * 2 ^ p + 14) + 10))) + 1))) + (14 * 2 ^ p + 11)) ∧
      Counters.Represents y.mem (y.regs forwardPointer)
        (WordTable.classCounters (as.map (BitVec.setWidth p)) (s.setWidth p)) ∧
      Counters.Represents y.mem (y.regs backwardPointer)
        (WordTable.classCounters (bs.map (BitVec.setWidth p)) (t.setWidth p)) ∧
      (∀ g : BitVec p, min (y.mem (y.regs forwardPointer + g.toNat))
        (y.mem (y.regs backwardPointer + (~~~g).toNat)) ≤ y.regs balance) ∧
      y.regs balance = Balance.prefixMax y.mem (y.regs forwardPointer)
        (y.regs backwardPointer) (2 ^ p) (2 ^ p) ∧ y.regs zero = 0 ∧
      (y.regs forwardPointer = B ∨ y.regs forwardPointer = B + 2 ^ p) ∧
      (y.regs backwardPointer = C ∨ y.regs backwardPointer = C + 2 ^ p) ∧
      (∀ z, z < q ∨ C + 2 * 2 ^ p ≤ z → y.mem z = x.mem z) := by
  obtain ⟨u, hu, uf, ur, up, uq, frame⟩ := countPair_exec as bs s t x ha hb
    haq hbq hqB hBr hrC hfitF hfitB
  obtain ⟨y, hy, ym, ya, yp, yq, yz⟩  := computeBalance_exec (N := 2 ^ p) u rfl rfl
    (hfitScan.of_le (by
      rcases up with h | h <;> rcases uq with h' | h' <;> rw [h, h'] <;> omega))
  refine ⟨y, hu.seq hy, ?_, ?_, ?_, ?_, yz, ?_, ?_, ?_⟩
  · simpa only [ym, yp] using uf
  · simpa only [ym, yq] using ur
  · intro g
    rw [ya, ym, yp, yq]
    rw [BitVec.toNat_not]
    exact Finset.le_sup (f := fun j => min (u.mem (u.regs forwardPointer + j))
      (u.mem (u.regs backwardPointer + (2 ^ p - 1 - j)))) (Finset.mem_range.mpr g.isLt)
  · simpa only [ym, yp, yq] using ya
  · rwa [yp]
  · rwa [yq]
  · intro z hz; rw [ym]; exact frame z hz

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
