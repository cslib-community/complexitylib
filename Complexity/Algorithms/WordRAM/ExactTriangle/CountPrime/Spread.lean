/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program
public import Complexity.Foundations.Data.Nat.Morton

/-!
# Computed native Morton spread table

The table may start dirty. Each entry is read only after an earlier native iteration has
written it, and its value follows the existing digit recurrence. Every division, remainder,
index calculation, load, store and loop instruction is charged. This is an internal stage
execution API; the complete counter must derive its constants, padded side and fit premises.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Only the scan and arithmetic/address temporaries change while constructing the table. -/
@[expose] def SpreadLocal (i : Fin 128) : Prop :=
  i = Reg.index ∨ i = Reg.address ∨ i = Reg.temporary ∨ i = Reg.position

instance (i : Fin 128) : Decidable (SpreadLocal i) :=
  inferInstanceAs (Decidable
    (i = Reg.index ∨ i = Reg.address ∨ i = Reg.temporary ∨ i = Reg.position))

/-- Construct all `2^k` actual spread words in at most `11*(2^k-1)+5` instructions,
preserving the caller memory outside exactly that table. -/
theorem exec_spreadTable {w k : ℕ} (x : Data 128)
    (hside : x.regs Reg.paddedSide = 2 ^ k)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1)
    (h2 : x.regs Reg.two = 2) (h4 : x.regs Reg.four = 4)
    (hw : Fits w (x.regs Reg.spread + 4 ^ k + 2 ^ k + 8)) :
    ∃ y, ExecWithin w spreadTable x y (11 * (2 ^ k - 1) + 5) ∧
      (∀ j < 2 ^ k, y.mem (x.regs Reg.spread + j) = Nat.Morton.spread j) ∧
      (∀ a, a < x.regs Reg.spread ∨ x.regs Reg.spread + 2 ^ k ≤ a → y.mem a = x.mem a) ∧
      ∀ i, ¬SpreadLocal i → y.regs i = x.regs i := by
  have hpow : 0 < 4 ^ k := by positivity
  have hsidePos : 0 < 2 ^ k := by positivity
  let I (y : Data 128) : Prop :=
    (∀ i, ¬SpreadLocal i → y.regs i = x.regs i) ∧
    1 ≤ y.regs Reg.index ∧ y.regs Reg.index ≤ 2 ^ k ∧
    (∀ j < y.regs Reg.index, y.mem (x.regs Reg.spread + j) = Nat.Morton.spread j) ∧
    ∀ a, ¬(x.regs Reg.spread ≤ a ∧ a < x.regs Reg.spread + y.regs Reg.index) →
      y.mem a = x.mem a
  have hbody (y : Data 128) (hy : I y) (hc : (Cond.lt Reg.index Reg.paddedSide).Holds y) :
      ∃ z, ExecWithin w spreadStep y z 9 ∧ I z ∧
        2 ^ k - z.regs Reg.index < 2 ^ k - y.regs Reg.index := by
    obtain ⟨hr, hlo, hhi, hv, hf⟩ := hy
    have hs := (hr Reg.paddedSide (by decide)).trans hside
    have hi : y.regs Reg.index < 2 ^ k := by simpa only [Cond.holds_lt, hs] using hc
    have hbase := hr Reg.spread (by decide)
    have hy1 := (hr Reg.one (by decide)).trans h1
    have hy2 := (hr Reg.two (by decide)).trans h2
    have hy4 := (hr Reg.four (by decide)).trans h4
    have hread : y.mem (y.regs Reg.spread + y.regs Reg.index / 2) =
        Nat.Morton.spread (y.regs Reg.index / 2) := by
      rw [hbase]
      apply hv
      omega
    have hvalue := Nat.Morton.spread_lt hi
    have hrec : Nat.Morton.spread (y.regs Reg.index / 2) * 4 + y.regs Reg.index % 2 =
        Nat.Morton.spread (y.regs Reg.index) := by
      rw [Nat.Morton.spread_eq (y.regs Reg.index)]
      omega
    have hquot : Fits w (y.regs Reg.index / 2) := hw.of_le (by omega)
    have hreadaddr : Fits w (y.regs Reg.spread + y.regs Reg.index / 2) := hw.of_le (by
      rw [hbase]; omega)
    have hprod : Fits w (Nat.Morton.spread (y.regs Reg.index / 2) * 4) :=
      hw.of_le (by omega)
    have hrem : Fits w (y.regs Reg.index % 2) := hw.of_le (by omega)
    have hsum : Fits w (Nat.Morton.spread (y.regs Reg.index)) := hw.of_le (by omega)
    have hwrite : Fits w (y.regs Reg.spread + y.regs Reg.index) := hw.of_le (by
      rw [hbase]; omega)
    have hinc : Fits w (y.regs Reg.index + 1) := hw.of_le (by omega)
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run =>
      ram_eval [spreadStep, hy1, hy2, hy4, hread, hquot, hreadaddr, hprod, hrem,
        hrec, hsum, hwrite, hinc, Reg.index, Reg.address, Reg.temporary, Reg.position,
        Reg.spread, Reg.one, Reg.two, Reg.four, Fin.mk.injEq]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hni
        have hne : i ≠ Reg.index ∧ i ≠ Reg.address ∧ i ≠ Reg.temporary ∧
            i ≠ Reg.position := by simpa only [SpreadLocal, not_or] using hni
        simpa only [Data.set, Data.write, Function.update_of_ne hne.1,
          Function.update_of_ne hne.2.1, Function.update_of_ne hne.2.2.1,
          Function.update_of_ne hne.2.2.2] using hr i hni
      · change 1 ≤ y.regs Reg.index + 1
        omega
      · change y.regs Reg.index + 1 ≤ 2 ^ k
        omega
      · intro j hj
        change j < y.regs Reg.index + 1 at hj
        change Function.update y.mem (y.regs Reg.spread + y.regs Reg.index)
          (Nat.Morton.spread (y.regs Reg.index)) (x.regs Reg.spread + j) = _
        by_cases he : j = y.regs Reg.index
        · subst j
          rw [hbase, Function.update_self]
        · rw [Function.update_of_ne (by rw [hbase]; omega)]
          exact hv j (by omega)
      · intro a ha
        change ¬(x.regs Reg.spread ≤ a ∧ a < x.regs Reg.spread + (y.regs Reg.index + 1)) at ha
        change Function.update y.mem (y.regs Reg.spread + y.regs Reg.index)
          (Nat.Morton.spread (y.regs Reg.index)) a = x.mem a
        rw [Function.update_of_ne (by rw [hbase]; omega)]
        apply hf
        omega
    case decrease =>
      change 2 ^ k - (y.regs Reg.index + 1) < 2 ^ k - y.regs Reg.index
      omega
  have hfit1 : Fits w 1 := hw.of_le (by omega)
  let y :=
    (((x.set Reg.address (x.regs Reg.spread)).write (x.regs Reg.spread) 0).set Reg.index 1)
  have hinit : ExecWithin w spreadSetup x y
      3 := by ram_eval [spreadSetup, y, h0, hfit1, Reg.address, Reg.spread, Reg.zero, Reg.index]
  have hI : I y := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hi' : i ≠ Reg.address ∧ i ≠ Reg.index := by
          simp only [SpreadLocal, not_or] at hi
          tauto
        simp only [y, Data.set, Data.write, Function.update_of_ne hi'.1,
          Function.update_of_ne hi'.2]
      · change 1 ≤ 1
        exact le_rfl
      · change 1 ≤ 2 ^ k
        omega
      · intro j hj
        change j < 1 at hj
        obtain rfl : j = 0 := by omega
        simp only [y, Nat.add_zero, Data.set, Data.write, Function.update_self,
          Nat.Morton.spread_zero]
      · intro a ha
        change ¬(x.regs Reg.spread ≤ a ∧ a < x.regs Reg.spread + 1) at ha
        change Function.update x.mem (x.regs Reg.spread) 0 a = x.mem a
        rw [Function.update_of_ne (show a ≠ x.regs Reg.spread by omega)]
  obtain ⟨z, hz, hIz, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => 2 ^ k - y.regs Reg.index) hbody hI
  have hrun := hinit.seq hz
  have hbound : 3 + ((2 ^ k - 1) * (9 + 2) + 2) ≤ 11 * (2 ^ k - 1) + 5 := by omega
  obtain ⟨hr, hlo, hhi, hv, hf⟩ := hIz
  have hi : z.regs Reg.index = 2 ^ k := by
    have hs := (hr Reg.paddedSide (by decide)).trans hside
    simp only [Cond.holds_lt, hs] at hstop
    omega
  refine ⟨z, hrun.mono hbound, ?_, ?_, hr⟩
  · simpa only [hi] using hv
  · intro a ha
    exact hf a (by omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
