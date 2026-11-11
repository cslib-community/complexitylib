/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORReachability
public import CslibFrontier.Computability.WordRAM.Notation
import Mathlib.Tactic.Linarith

/-!
# Native Add/XNOR reachable-state sweeps

[WangLvShenZhang2027], Observation 1, PDF p. 20. The code uses two
nonoverlapping arrays of Boolean flags. Every output flag is obtained by two
indexed loads at the actual inverse-addition and inverse-XNOR addresses.
All arithmetic, loads, stores and loop tests are ordinary standard-basis
WordRAM instructions; no Lean function is executed as an instruction.

The physical word width must fit both buffers and intermediate addresses.
One flag occupies one physical word, not one bit. The input table is supplied
in memory; this module does not silently charge its construction as free.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native

open Cslib.WordRAM

/-- Source buffer base. -/
abbrev source : Fin 18 := 0
/-- Destination buffer base. -/
abbrev destination : Fin 18 := 1
/-- State modulus, `2^m`. -/
abbrev modulus : Fin 18 := 2
/-- Actual operand, less than the state modulus. -/
abbrev operand : Fin 18 := 3
/-- Current output state. -/
abbrev index : Fin 18 := 4
/-- Constant one. -/
abbrev one : Fin 18 := 5
/-- Indexed memory address. -/
abbrev address : Fin 18 := 6
/-- First predecessor flag. -/
abbrev left : Fin 18 := 7
/-- Second predecessor flag. -/
abbrev right : Fin 18 := 8
/-- The `m`-bit all-ones mask. -/
abbrev mask : Fin 18 := 9
/-- Nonnegative additive inverse before reduction. -/
abbrev negative : Fin 18 := 10
/-- Union of predecessor flags. -/
abbrev value : Fin 18 := 11

/-- One table entry: address arithmetic, two loads, Boolean union and one store. -/
@[expose] def body : Code .standard 18 := ram[
  left ← negative + index; left ← left % modulus;
  address ← source + left; left ← *address;
  right ← index ^^^ mask; right ← right ^^^ operand;
  address ← source + right; right ← *address;
  value ← left ||| right; address ← destination + index;
  *address ← value; index ← index + one ]

/-- A single fixed program sweeps all states at every supplied width. -/
@[expose] def sweep : Code .standard 18 :=
  .seq (ram[ index ← #0; one ← #1; mask ← modulus - one;
    negative ← modulus - operand ]) (.loop (.lt index modulus) body)

/-- Mathematical specification of an updated updatePrefix; not an executable primitive. -/
def updatePrefix (mem : ℕ → ℕ) (b c N a k : ℕ) : ℕ → ℕ :=
  fun z => if c ≤ z ∧ z < c + k then
    mem (b + ((N - a + (z - c)) % N)) |||
      mem (b + (((z - c) ^^^ (N - 1)) ^^^ a)) else mem z

private theorem updatePrefix_zero (mem : ℕ → ℕ) (b c N a : ℕ) :
    updatePrefix mem b c N a 0 = mem := by
  funext z
  simp [updatePrefix]

private theorem updatePrefix_succ (mem : ℕ → ℕ) (b c N a k : ℕ) :
    updatePrefix mem b c N a (k + 1) = Function.update (updatePrefix mem b c N a k) (c + k)
      (mem (b + ((N - a + k) % N)) ||| mem (b + ((k ^^^ (N - 1)) ^^^ a))) := by
  funext z
  by_cases hz : z = c + k
  · subst z; simp [updatePrefix]
  · simp only [updatePrefix, Function.update_of_ne hz]
    have h : (c ≤ z ∧ z < c + (k + 1)) ↔ (c ≤ z ∧ z < c + k) := by omega
    simp only [h]

/-- Every initialized output cell contains the actual union of predecessor flags. -/
theorem updatePrefix_read (mem : ℕ → ℕ) (b c N a k j : ℕ) (hj : j < k) :
    updatePrefix mem b c N a k (c + j) =
      mem (b + ((N - a + j) % N)) ||| mem (b + ((j ^^^ (N - 1)) ^^^ a)) := by
  simp [updatePrefix, hj]

/-- No store outside the destination updatePrefix is hidden by the specification. -/
theorem updatePrefix_outside (mem : ℕ → ℕ) (b c N a k z : ℕ)
    (hz : ¬(c ≤ z ∧ z < c + k)) : updatePrefix mem b c N a k z = mem z := by
  simp [updatePrefix, hz]

/-- Native full-array execution, including initialization of scratch registers and
all loop control. Only the destination buffer changes. Dirty destination memory
is permitted. A supplied Boolean source table is required, not presumed free. -/
theorem sweep_exec {W m b c a : ℕ} (x : Data 18)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (ha : x.regs operand = a)
    (haN : a < 2 ^ m) (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hflags : ∀ j < 2 ^ m, x.mem (b + j) < 2)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2)) :
    ∃ y, ExecWithin W sweep x y (14 * 2 ^ m + 6) ∧
      y.mem = updatePrefix x.mem b c (2 ^ m) a (2 ^ m) ∧
      y.regs source = b ∧ y.regs destination = c ∧
      y.regs modulus = 2 ^ m ∧ y.regs operand = a := by
  have hN : 0 < 2 ^ m := Nat.two_pow_pos m
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hmask : Fits W (2 ^ m - 1) := hfit.of_le (by omega)
  have hneg : Fits W (2 ^ m - a) := hfit.of_le (by omega)
  let start := (((x.set index 0).set one 1).set mask (2 ^ m - 1)).set negative (2 ^ m - a)
  have hs : ExecWithin (B := .standard) W
      (ram[ index ← #0; one ← #1; mask ← modulus - one; negative ← modulus - operand ])
      x start 4 := by
    ram_eval [start, hb, hc, hn, ha, h0, h1, hmask, hneg,
      source, destination, modulus, operand, index, one, mask, negative, Fin.mk.injEq]
  let I (y : Data 18) : Prop :=
    y.regs source = b ∧ y.regs destination = c ∧ y.regs modulus = 2 ^ m ∧
    y.regs operand = a ∧ y.regs one = 1 ∧ y.regs mask = 2 ^ m - 1 ∧
    y.regs negative = 2 ^ m - a ∧ y.regs index ≤ 2 ^ m ∧
    y.mem = updatePrefix x.mem b c (2 ^ m) a (y.regs index)
  have hi : I start := by
    simp [I, start, updatePrefix_zero, hb, hc, hn, ha,
      source, destination, modulus, operand, index, one, mask, negative]
  have step (y : Data 18) (hy : I y) (ht : (Cond.lt index modulus).Holds y) :
      ∃ z, ExecWithin W body y z 12 ∧ I z ∧
        2 ^ m - z.regs index < 2 ^ m - y.regs index := by
    obtain ⟨yb, yc, yn, ya, yo, ym, yg, yi, ymem⟩ := hy
    have hj : y.regs index < 2 ^ m := by simpa only [Cond.holds_lt, yn] using ht
    have hx1 := Nat.xor_lt_two_pow hj (show 2 ^ m - 1 < 2 ^ m by omega)
    have hx2 := Nat.xor_lt_two_pow hx1 haN
    have hadd : Fits W (2 ^ m - a + y.regs index) := hfit.of_le (by omega)
    have hmod : Fits W ((2 ^ m - a + y.regs index) % 2 ^ m) :=
      hfit.of_le (by have := Nat.mod_lt (2 ^ m - a + y.regs index) hN; omega)
    have hxor1 : Fits W (y.regs index ^^^ (2 ^ m - 1)) := hfit.of_le (by omega)
    have hxor2 : Fits W ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a) := hfit.of_le (by omega)
    have haddr1 : Fits W (b + ((2 ^ m - a + y.regs index) % 2 ^ m)) :=
      hfit.of_le (by have := Nat.mod_lt (2 ^ m - a + y.regs index) hN; omega)
    have haddr2 : Fits W (b + ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a)) :=
      hfit.of_le (by omega)
    have haddr3 : Fits W (c + y.regs index) := hfit.of_le (by omega)
    have hnext : Fits W (y.regs index + 1) := hfit.of_le (by omega)
    have hread (j : ℕ) (hj : j < 2 ^ m) : y.mem (b + j) = x.mem (b + j) := by
      rw [ymem, updatePrefix_outside]
      rcases hdisjoint with hd | hd <;> omega
    let l := x.mem (b + ((2 ^ m - a + y.regs index) % 2 ^ m))
    let r := x.mem (b + ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a))
    have hl : l < 2 := hflags _ (Nat.mod_lt _ hN)
    have hr : r < 2 := hflags _ hx2
    have hv : Fits W (l ||| r) := by
      have := Nat.or_lt_two_pow (n := 1) hl hr
      exact hfit.of_le (by norm_num at this; omega)
    let z := y.set left (2 ^ m - a + y.regs index)
      |>.set left ((2 ^ m - a + y.regs index) % 2 ^ m)
      |>.set address (b + ((2 ^ m - a + y.regs index) % 2 ^ m))
      |>.set left l
      |>.set right (y.regs index ^^^ (2 ^ m - 1))
      |>.set right ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a)
      |>.set address (b + ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a))
      |>.set right r
      |>.set value (l ||| r)
      |>.set address (c + y.regs index)
      |>.write (c + y.regs index) (l ||| r)
      |>.set index (y.regs index + 1)
    have he : ExecWithin W body y z 12 := by
      ram_eval [body, z, l, r, yb, yc, yn, ya, yo, ym, yg,
        hread _ (Nat.mod_lt _ hN), hread _ hx2, hadd, hmod, hxor1, hxor2,
        haddr1, haddr2, haddr3, hnext, hv, source, destination, modulus,
        operand, index, one, address, left, right, mask, negative, value, Fin.mk.injEq]
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide only [z, Data.set_regs, Data.set_mem,
        Data.write_regs, Data.write_mem, Function.update_apply, source, destination,
        modulus, operand, index, one, address, left, right, mask, negative, value,
        ↓reduceIte]
      · exact yb
      · exact yc
      · exact yn
      · exact ya
      · exact yo
      · exact ym
      · exact yg
      · simpa only [index] using (Nat.succ_le_iff.mpr hj)
      · simpa only [l, r, ymem] using (updatePrefix_succ x.mem b c (2 ^ m) a (y.regs index)).symm
    · simp only [z, Data.set_regs, Function.update_self]
      omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I (fun y => 2 ^ m - y.regs index) step hi
  have hj : y.regs index = 2 ^ m := by
    have := hy.2.2.2.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.2.1] at ht
    omega
  refine ⟨y, ?_, ?_, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩
  · apply (hs.seq he).mono
    have hstart : start.regs index = 0 := by simp [start, index, one, mask, negative]
    rw [hstart]
    omega
  · simpa only [hj] using hy.2.2.2.2.2.2.2.2

/-- A buffer represents a truth table on actual words. -/
@[expose] def Represents {m : ℕ} (mem : ℕ → ℕ) (b : ℕ) (table : WordTable Bool m) : Prop :=
  ∀ s : BitVec m, mem (b + s.toNat) = (table.read s).toNat

/-- Representation entails the Boolean source requirement, including width zero. -/
theorem Represents.flags {m : ℕ} {mem : ℕ → ℕ} {b : ℕ} {table : WordTable Bool m}
    (h : Represents mem b table) : ∀ j < 2 ^ m, mem (b + j) < 2 := by
  intro j hj
  have hs := h (BitVec.ofNat m j)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at hs
  rw [hs]
  cases table.read (BitVec.ofNat m j) <;> decide

/-- The native addresses are the actual modular inverses used by the semantic DP. -/
theorem updatePrefix_represents {m : ℕ} (mem : ℕ → ℕ) (b c : ℕ) (a : BitVec m)
    (table : WordTable Bool m) (h : Represents mem b table) :
    Represents (updatePrefix mem b c (2 ^ m) a.toNat (2 ^ m)) c
      (WordTable.advance (stateKey a) table).ret := by
  intro s
  rw [updatePrefix_read _ _ _ _ _ _ _ s.isLt, WordTable.advance_read]
  have hadd := h (s - a)
  have hxor := h (s ^^^ (~~~a))
  rw [BitVec.toNat_sub] at hadd
  rw [BitVec.toNat_xor, BitVec.toNat_not] at hxor
  have hmask : (s.toNat ^^^ (2 ^ m - 1)) ^^^ a.toNat =
      s.toNat ^^^ (2 ^ m - 1 - a.toNat) := by
    have he := congrArg BitVec.toNat
      (show s ^^^ BitVec.allOnes m ^^^ a = s ^^^ (~~~a) by
        rw [BitVec.xor_assoc, BitVec.allOnes_xor])
    simpa only [BitVec.toNat_xor, BitVec.toNat_not, Nat.xor_comm,
      Nat.xor_assoc, BitVec.toNat_allOnes] using he
  rw [hmask, hadd, hxor]
  simp only [unstep, Bool.false_eq_true, ↓reduceIte,
    BitVec.not_xor_right]
  cases table.read (s - a) <;> cases table.read (s ^^^ ~~~a) <;> decide

/-- One native layer refines the unrestricted semantic layer. -/
theorem advance_exec {W m b c : ℕ} (x : Data 18) (a : BitVec m)
    (table : WordTable Bool m) (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (ha : x.regs operand = a.toNat)
    (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hrep : Represents x.mem b table) (hfit : Fits W (b + c + 2 * 2 ^ m + 2)) :
    ∃ y, ExecWithin W sweep x y (14 * 2 ^ m + 6) ∧
      Represents y.mem c (WordTable.advance (stateKey a) table).ret ∧
      y.mem = updatePrefix x.mem b c (2 ^ m) a.toNat (2 ^ m) ∧
      y.regs source = b ∧ y.regs destination = c ∧
      y.regs modulus = 2 ^ m ∧ y.regs operand = a.toNat := by
  obtain ⟨y, he, hm, hr⟩ := sweep_exec x hb hc hn ha a.isLt hdisjoint hrep.flags hfit
  exact ⟨y, he, hm ▸ updatePrefix_represents x.mem b c a table hrep, hm, hr⟩

end Cslib.Cryptanalysis.AddXNOR.Native
