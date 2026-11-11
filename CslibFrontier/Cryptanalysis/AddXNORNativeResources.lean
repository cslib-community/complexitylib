/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeRun
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.TraceBounds
import Mathlib.Tactic.Linarith

/-!
# Complete native Add/XNOR decision and memory resources

[WangLvShenZhang2027], Observation 1, PDF p. 20. Memory cells 1--4
contain width, initial word, target and operand count; operands follow at cell 5.
The program reads the header, constructs `2^m` with a charged shift, places two
reusable buffers immediately after the input, initializes the first buffer,
executes every layer and returns its target flag. No table is provided for free.

The word width is logarithmic in `3 * 2^m + 2q + 12`. The proved bound counts
ordinary standard-basis instructions and bounds the union of every accessed
cell in the actual transcript, hence also peak cells, with each cell holding a
word of that width. This is a native WordRAM result, not a multitape bit-time
simulation or the paper's sorted-list output-sensitive refinement.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native

open Cslib.WordRAM

/-- Read the actual input header and compute the buffer layout using native instructions. -/
@[expose] def setup : Code .standard 18 := ram[
  address ← #1; modulus ← *address; one ← #1; modulus ← one <<< modulus;
  address ← #2; initial ← *address; address ← #3; target ← *address;
  address ← #4; limit ← *address; cursor ← #5; limit ← limit + cursor;
  source ← limit; destination ← source + modulus ]

/-- One fixed structured program, independent of every input parameter. -/
@[expose] def entry : Code .standard 18 := .seq setup decide

/-- Physical word width; this is an encoding/layout choice, not an assigned program cost. -/
@[expose] def wordWidth (m q : ℕ) : ℕ := (3 * 2 ^ m + 2 * q + 12).log2 + 1

/-- The chosen width fits the layout and all larger scratch values used in the proof. -/
theorem layout_fits (m q : ℕ) : Fits (wordWidth m q) (3 * 2 ^ m + 2 * q + 12) :=
  Nat.lt_log2_self

/-- Explicit address capacity is linear in the table and input sizes. -/
theorem address_capacity (m q : ℕ) :
    2 ^ wordWidth m q ≤ 6 * 2 ^ m + 4 * q + 24 := by
  have hp := Nat.log2_self_le (n := 3 * 2 ^ m + 2 * q + 12) (by omega)
  simp only [wordWidth, pow_succ]
  omega

/-- Input-header execution is charged, and the complete native decision refines
actual full-width solvability. All cells at or below the end of the input survive. -/
theorem entry_exec {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) (x : Data 18)
    (hm : x.mem 1 = m) (hs : x.mem 2 = s.toNat) (ht : x.mem 3 = t.toNat)
    (hq : x.mem 4 = as.length)
    (hinput : ∀ j (hj : j < as.length), x.mem (5 + j) = as[j].toNat) :
    ∃ y, ExecWithin (wordWidth m as.length) entry x y
        (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 26) ∧
      (y.regs answer = 1 ↔ Solvable as s t) ∧ y.regs answer < 2 ∧
      (∀ z, z < as.length + 5 → y.mem z = x.mem z) := by
  have hfit := layout_fits m as.length
  have h1 : Fits (wordWidth m as.length) 1 := hfit.of_le (by omega)
  have h2 : Fits (wordWidth m as.length) 2 := hfit.of_le (by omega)
  have h3 : Fits (wordWidth m as.length) 3 := hfit.of_le (by omega)
  have h4 : Fits (wordWidth m as.length) 4 := hfit.of_le (by omega)
  have h5 : Fits (wordWidth m as.length) 5 := hfit.of_le (by omega)
  have hN : Fits (wordWidth m as.length) (2 ^ m) := hfit.of_le (by omega)
  have hend : Fits (wordWidth m as.length) (as.length + 5) := hfit.of_le (by omega)
  have hbuffer : Fits (wordWidth m as.length) (as.length + 5 + 2 ^ m) := hfit.of_le (by omega)
  let z := x.set address 1
    |>.set modulus m |>.set one 1 |>.set modulus (2 ^ m)
    |>.set address 2 |>.set initial s.toNat
    |>.set address 3 |>.set target t.toNat
    |>.set address 4 |>.set limit as.length |>.set cursor 5
    |>.set limit (as.length + 5) |>.set source (as.length + 5)
    |>.set destination (as.length + 5 + 2 ^ m)
  have heSetup : ExecWithin (wordWidth m as.length) setup x z 14 := by
    ram_eval [setup, z, hm, hs, ht, hq, h1, h2, h3, h4, h5, hN, hend, hbuffer,
      Nat.shiftLeft_eq, one_mul, address, modulus, one, initial, target, limit, cursor,
      source, destination, Fin.mk.injEq]
  have zb : z.regs source = as.length + 5 := by
    simp +decide [z, source, destination]
  have zc : z.regs destination = as.length + 5 + 2 ^ m := by simp [z]
  have zn : z.regs modulus = 2 ^ m := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  have zp : z.regs cursor = 5 := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  have zl : z.regs limit = 5 + as.length := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination,
      Nat.add_comm]
  have zs : z.regs initial = s.toNat := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  have zt : z.regs target = t.toNat := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  obtain ⟨y, heDecide, hy, hbool, hframe⟩ := decide_exec as s t z zb zc zn zp zl zs zt
    hinput (by intro j hj; simp only [InBuffers]; omega) (Or.inl (by omega))
    (hfit.of_le (by omega)) (hfit.of_le (by omega))
  refine ⟨y, (heSetup.seq heDecide).mono (by omega), hy, hbool, ?_⟩
  intro j hj
  exact hframe j (by simp only [InBuffers]; omega)

/-- Native deterministic machine code. No random instruction or width-specific
code generation occurs; width affects only the admitted input representation. -/
theorem entry_fixed : entry.IsRandFree ∧ ¬entry.ReadsWidth := by decide

/-- The complete exact native execution has the advertised exponential time and
linear-table address footprint, including its halting instruction. The footprint
contains every cell ever read or written, so it bounds peak cells as well.
Multiply the cell/register bound by `wordWidth m q` for stored bits; a separate
bit-time simulation is not asserted. -/
theorem entry_resources {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) (x : Data 18)
    (hx : x.Bounded (wordWidth m as.length))
    (hm : x.mem 1 = m) (hs : x.mem 2 = s.toNat) (ht : x.mem 3 = t.toNat)
    (hq : x.mem 4 = as.length)
    (hinput : ∀ j (hj : j < as.length), x.mem (5 + j) = as[j].toNat) :
    ∃ y n ts,
      n ≤ 4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 26 ∧
      TraceExec (wordWidth m as.length) entry x y n ts ∧
      Executes (wordWidth m as.length) (entry.program answer) ⟨0, x⟩ (y.regs answer) (n + 1) ∧
      (y.regs answer = 1 ↔ Solvable as s t) ∧ y.regs answer < 2 ∧
      (Probe.reads ts ∪ Probe.writes ts).card ≤ 6 * 2 ^ m + 4 * as.length + 24 := by
  obtain ⟨y, ⟨n, hn, he⟩, hy, hbool, _⟩ := entry_exec as s t x hm hs ht hq hinput
  obtain ⟨ts, htrace⟩ := he.exists_trace
  exact ⟨y, n, ts, hn, htrace, he.executes answer, hy, hbool,
    (htrace.address_footprint_le hx).trans (address_capacity m as.length)⟩

/-- Standard input words: width, initial state, target, count, then actual operands. -/
@[expose] def encodeInput {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) : List ℕ :=
  [m, s.toNat, t.toNat, as.length] ++ as.map BitVec.toNat

/-- The entire encoded input fits the chosen physical width. -/
theorem encodeInput_fits {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    InputFits (wordWidth m as.length) (encodeInput as s t) := by
  have hfit := layout_fits m as.length
  refine ⟨hfit.of_le (by simp [encodeInput]; omega), ?_⟩
  intro v hv
  simp only [encodeInput, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hv
  have hmN := Nat.lt_two_pow_self (n := m)
  rcases hv with (rfl | rfl | rfl | rfl) | ⟨a, _, rfl⟩
  · exact hfit.of_le (by omega)
  · exact hfit.of_le (by have := s.isLt; omega)
  · exact hfit.of_le (by have := t.isLt; omega)
  · exact hfit.of_le (by omega)
  · exact hfit.of_le (by have := a.isLt; omega)

private theorem encoded_operand {m : ℕ} (as : List (BitVec m)) (s t : BitVec m)
    (j : ℕ) (hj : j < as.length) :
    (Data.init (encodeInput as s t) : Data 18).mem (5 + j) = as[j].toNat := by
  rw [show 5 + j = (j + 4) + 1 by omega, Data.init_mem_succ,
    List.getD_eq_getElem?_getD]
  rw [encodeInput, List.getElem?_append_right (by change 4 ≤ j + 4; omega)]
  simp [List.getElem?_eq_getElem hj]

/-- A conventional input-to-halt certificate for every width and every instance. -/
theorem encoded_answers {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    (entry.program answer).Answers (wordWidth m as.length) (encodeInput as s t)
      (Solvable as s t) (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 27) := by
  obtain ⟨y, he, hy, hbool, _⟩ := entry_exec as s t (Data.init (encodeInput as s t))
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (encoded_operand as s t)
  exact (show entry.Answers answer (wordWidth m as.length) (encodeInput as s t)
    (Solvable as s t) (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 26) from
    ⟨y, he, by omega, hy⟩).program

/-- Actual transcript and halting resources from the standard input convention. -/
theorem encoded_resources {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    ∃ y n ts,
      n ≤ 4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 26 ∧
      TraceExec (wordWidth m as.length) entry (Data.init (encodeInput as s t)) y n ts ∧
      Executes (wordWidth m as.length) (entry.program answer) (State.init (encodeInput as s t))
        (y.regs answer) (n + 1) ∧
      (y.regs answer = 1 ↔ Solvable as s t) ∧ y.regs answer < 2 ∧
      (Probe.reads ts ∪ Probe.writes ts).card ≤ 6 * 2 ^ m + 4 * as.length + 24 :=
  entry_resources as s t (Data.init (encodeInput as s t))
    (Data.Bounded.init (encodeInput_fits as s t))
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (encoded_operand as s t)

/-- The flat program has constant size, including its final halt. -/
theorem program_length : (entry.program answer).length = 56 := by decide

/-- Native instruction time and peak accessed storage, including the register
bank, in the conventional exponential form. The bounds follow from the actual
halting execution and transcript, and remain valid for empty/zero-width inputs. -/
theorem encoded_time_space {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    ∃ y n ts,
      n + 1 ≤ 45 * (as.length + 1) * 2 ^ m ∧
      TraceExec (wordWidth m as.length) entry (Data.init (encodeInput as s t)) y n ts ∧
      Executes (wordWidth m as.length) (entry.program answer) (State.init (encodeInput as s t))
        (y.regs answer) (n + 1) ∧
      (y.regs answer = 1 ↔ Solvable as s t) ∧
      ((Probe.reads ts ∪ Probe.writes ts).card + 18) * wordWidth m as.length ≤
        (6 * 2 ^ m + 4 * as.length + 42) * wordWidth m as.length := by
  obtain ⟨y, n, ts, hn, htrace, he, hy, _, hspace⟩ := encoded_resources as s t
  refine ⟨y, n, ts, ?_, htrace, he, hy, ?_⟩
  · have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hq := Nat.mul_le_mul_left as.length hp
    nlinarith
  · exact Nat.mul_le_mul_right _ (by omega)

end Cslib.Cryptanalysis.AddXNOR.Native
