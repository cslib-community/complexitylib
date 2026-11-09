/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
public import CslibFrontier.Computability.WordRAM.TraceParameters
public import CslibFrontier.Computability.WordRAM.ListArray
import all CslibFrontier.Computability.WordRAM.Structured

/-!
# Charged native serialization of packed operator words

The fixed loop writes one actual zero/one word per operator, including leading
zero operators. Reversed output changes the destination cursor rather than
reversing a host list for free. The theorem derives finite execution, exact array
contents and outside-memory frames from physical registers and word capacity.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter.OutputBits

open Cslib.WordRAM

/-- Unconsumed packed word. -/
abbrev value : Fin 7 := 0
/-- Remaining operator count. -/
abbrev remaining : Fin 7 := 1
/-- Destination cursor. -/
abbrev cursor : Fin 7 := 2
/-- Current output bit. -/
abbrev bit : Fin 7 := 3
/-- Constant one. -/
abbrev one : Fin 7 := 4
/-- Constant two. -/
abbrev two : Fin 7 := 5
/-- Constant zero. -/
abbrev zero : Fin 7 := 6

/-- One bit, one store and a cursor movement in the selected order. -/
@[expose] def body (back : Bool) : Code .standard 7 :=
  .seq (ram[ bit ← value % two; *cursor ← bit; value ← value / two;
    remaining ← remaining - one ])
    (if back then ram[ cursor ← cursor - one ] else ram[ cursor ← cursor + one ])

/-- Fixed-size loop; the packed word, count and initial cursor are registers. -/
@[expose] def program (back : Bool) : Code .standard 7 :=
  .seq (ram[ one ← #1; two ← #2; zero ← #0 ])
    (.loop (.lt zero remaining) (body back))

/-- The concrete word array produced by a packed word. -/
def words (back : Bool) (n v : ℕ) : List ℕ :=
  ((if back then (decode n v).reverse else decode n v)).map Bool.toNat

/-- Exactly one output word per operator, at arbitrary admitted widths. -/
theorem words_length (back : Bool) (n v : ℕ) : (words back n v).length = n := by
  cases back <;> simp [words, decode_length]

private theorem loop_exec {W n b v : ℕ} (back : Bool) (x : Data 7)
    (hn : x.regs remaining = n) (hv : x.regs value = v)
    (hb : x.regs cursor = if back then b + n - 1 else b)
    (h1 : x.regs one = 1) (h2 : x.regs two = 2) (h0 : x.regs zero = 0)
    (hfv : Fits W v) (hfit : Fits W (b + n + 3)) :
    ∃ y, ExecWithin W (.loop (.lt zero remaining) (body back)) x y (7 * n + 2) ∧
      Block.HoldsList b (words back n v) y.mem ∧
      (∀ a, a < b ∨ b + n ≤ a → y.mem a = x.mem a) := by
  induction n generalizing b v x with
  | zero =>
    refine ⟨x, ?_, ?_, fun _ _ => rfl⟩
    · exact ExecWithin.loop_exit (by simp only [Cond.holds_lt, h0, hn]; omega)
    · simpa only [words, decode, List.reverse_nil, ite_self, List.map_nil]
        using Block.holdsList_nil b x.mem
  | succ n ih =>
    have hrem : v % 2 = (decide (v % 2 = 1)).toNat := by
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    let addr := if back then b + n else b
    let next := if back then addr - 1 else addr + 1
    let z := x.set bit (v % 2) |>.write addr (v % 2) |>.set value (v / 2)
      |>.set remaining n |>.set cursor next
    have ha : Fits W addr := hfit.of_le (by dsimp [addr]; split <;> omega)
    have hr : Fits W (v % 2) := hfit.of_le (by have := Nat.mod_lt v (by decide : 0 < 2); omega)
    have hd : Fits W (v / 2) := hfv.of_le (Nat.div_le_self _ _)
    have hnfit : Fits W n := hfit.of_le (by omega)
    have hc : Fits W next := hfit.of_le (by dsimp [next, addr]; split <;> omega)
    have actual : x.regs cursor = addr := by
      cases back <;> simp only [addr, Bool.false_eq_true, ↓reduceIte] at * <;> omega
    have hplus : Fits W (b + 1) := hfit.of_le (by omega)
    have hminus : Fits W (b + n - 1) := hfit.of_le (by omega)
    have step : ExecWithin W (body back) x z 5 := by
      cases back <;>
        ram_eval [body, z, addr, next, h1, h2, hn, hv, actual, ha, hr, hd, hnfit, hc, hplus, hminus,
          value, remaining, cursor, bit, one, two, zero, Fin.mk.injEq, Nat.add_sub_cancel,
          Nat.add_sub_assoc, Nat.add_assoc]
    have zcount : z.regs remaining = n := by simp +decide [z, remaining, cursor]
    have zvalue : z.regs value = v / 2 := by simp +decide [z, value, remaining, cursor]
    have zcursor : z.regs cursor = if back then (if back then b else b + 1) + n - 1
        else b + 1 := by
      cases back <;> simp [z, next, addr]
    obtain ⟨y, he, contents, frame⟩ := ih (b := if back then b else b + 1)
      (v := v / 2) z zcount zvalue (by cases back <;> simpa using zcursor)
      (by simpa +decide [z, one, bit, value, remaining, cursor] using h1)
      (by simpa +decide [z, two, bit, value, remaining, cursor] using h2)
      (by simpa +decide [z, zero, bit, value, remaining, cursor] using h0)
      hd (hfit.of_le (by cases back <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega))
    refine ⟨y, ?_, ?_, ?_⟩
    · exact (ExecWithin.loop_iter
        (by simp only [Cond.holds_lt, h0, hn]; omega) step he).mono (by omega)
    · cases back
      · have head : Block.HoldsList b [v % 2] y.mem := by
          intro i
          have hi : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
          change y.mem (b + i.val) = [v % 2][i.val]
          simp only [hi, Nat.add_zero, List.getElem_cons_zero]
          rw [frame _ (by simp)]
          simp [z, addr, Data.write_mem]
        have hh := head.append contents
        simpa only [words, Bool.false_eq_true, ↓reduceIte, decode, List.map_cons,
          List.singleton_append, ← hrem, List.length_singleton] using hh
      · have tail : Block.HoldsList (b + n) [v % 2] y.mem := by
          intro i
          have hi : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
          change y.mem (b + n + i.val) = [v % 2][i.val]
          simp only [hi, Nat.add_zero, List.getElem_cons_zero]
          rw [frame _ (by simp)]
          simp [z, addr, Data.write_mem]
        have hh := contents.append (by
          simpa only [words_length, Bool.true_eq, ↓reduceIte] using tail)
        simpa only [words, Bool.true_eq, ↓reduceIte, decode, List.reverse_cons, List.map_append,
          List.map_cons, List.map_nil, ← hrem] using hh
    · intro a ha'
      rw [frame a (by cases back <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)]
      change Function.update x.mem addr (v % 2) a = x.mem a
      exact Function.update_of_ne (by dsimp [addr]; split <;> omega) _ _

/-- Actual packed-word serialization. Time includes setup and all loop tests;
stores, native control and every continuing prefix are charged by this execution. -/
theorem exec {W n b v : ℕ} (back : Bool) (x : Data 7)
    (hn : x.regs remaining = n) (hv : x.regs value = v)
    (hb : x.regs cursor = if back then b + n - 1 else b)
    (hfv : Fits W v) (hfit : Fits W (b + n + 3)) :
    ∃ y, ExecWithin W (program back) x y (7 * n + 5) ∧
      Block.HoldsList b (words back n v) y.mem ∧
      (∀ a, a < b ∨ b + n ≤ a → y.mem a = x.mem a) := by
  let z := x.set one 1 |>.set two 2 |>.set zero 0
  have hs : ExecWithin (B := .standard) W (ram[ one ← #1; two ← #2; zero ← #0 ]) x z 3 := by
    have h1 : Fits W 1 := hfit.of_le (by omega)
    have h2 : Fits W 2 := hfit.of_le (by omega)
    ram_eval [z, h1, h2, fits_zero W, one, two, zero, Fin.mk.injEq]
  obtain ⟨y, he, contents, frame⟩ := loop_exec back z
    (by simpa +decide [z, remaining, one, two, zero] using hn)
    (by simpa +decide [z, value, one, two, zero] using hv)
    (by simpa +decide [z, cursor, one, two, zero] using hb)
    (by simp +decide [z, one, two, zero]) (by simp +decide [z, two, zero]) (by simp [z]) hfv hfit
  exact ⟨y, (hs.seq he).mono (by omega), contents, frame⟩

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter.OutputBits
