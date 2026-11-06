/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeQuery

/-!
# Native full-state recovery on quarter bucket hits

The full second quarter is evaluated only for records reached through a matching
low-bit bucket. Output records contain the actual full state and both packed
quarter witnesses. All pointer/list/admin operations are ordinary instructions.
This emitter materializes its output and is appropriate for the retained side;
a streaming dictionary consumer must instead process each hit without retaining
the whole opposite class. It is not the complete dissection program.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Next free output cell. -/
abbrev output : Fin 32 := 24
/-- First-quarter witness of the current hit. -/
abbrev firstOperators : Fin 32 := 25
/-- Zero used in the linked-list termination test. -/
abbrev zero : Fin 32 := 26

/-- One full-state output record, with exact machine store order. -/
def emitMemory (mem : ℕ → ℕ) (o s u v : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update mem o s) (o + 1) u) (o + 2) v

/-- Load one hit, recover its full second-quarter state and emit three words. -/
@[expose] def emitBody : Code .standard 32 :=
  .seq (ram[ address ← link + one; state ← *address; address ← address + one;
    firstOperators ← *address; link ← *link ])
    (.seq evaluate (ram[ *output ← state; output ← output + one;
      *output ← firstOperators; output ← output + one;
      *output ← operators; output ← output + one ]))

/-- Terminate at the null pointer; native test and jump are charged per hit. -/
@[expose] def emitLoop : Code .standard 32 := .loop (.lt zero link) emitBody

/-- Exact output memory after recovering a list of matching first-quarter hits. -/
def emittedMemory {m : ℕ} (as : List (BitVec m)) (v : ℕ) :
    List (ℕ × ℕ) → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], mem, _ => mem
  | (s, u) :: rs, mem, o => emittedMemory as v rs
      (emitMemory mem o (eval ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat u v) (o + 3)

/-- The hit emitter changes only its output interval. -/
theorem emitMemory_outside (mem : ℕ → ℕ) (o s u v a : ℕ)
    (ha : ¬(o ≤ a ∧ a < o + 3)) : emitMemory mem o s u v a = mem a := by
  simp [emitMemory, show a ≠ o by omega, show a ≠ o + 1 by omega, show a ≠ o + 2 by omega]

/-- Recover and output exactly the linked hits. The read-only boundary protects
both the quarter bucket and the original second-quarter operands. The output
pointer, stores and loop control are included in the bound. No list of nonhits
is traversed and no host chain evaluation is used as an instruction. -/
theorem emitLoop_exec {W m b boundary ptr o v : ℕ} (as : List (BitVec m))
    (rs : List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (ho : x.regs output = o)
    (hone : x.regs one = 1) (hz : x.regs zero = 0)
    (hlinked : Linked x.mem boundary ptr rs) (hout : boundary ≤ o)
    (hinputEnd : b + as.length ≤ boundary)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hstates : ∀ r ∈ rs, r.1 < 2 ^ m)
    (hfit : Fits W (boundary + o + 3 * rs.length + 2 * 2 ^ m + b + as.length + 4)) :
    ∃ y, ExecWithin W emitLoop x y (rs.length * (11 * as.length + 20) + 2) ∧
      y.mem = emittedMemory as v rs x.mem o ∧
      y.regs output = o + 3 * rs.length ∧ y.regs link = 0 := by
  induction rs generalizing x ptr o with
  | nil =>
    cases hlinked
    refine ⟨x, ?_, rfl, by simpa using ho, hl⟩
    simpa only [List.length_nil, Nat.zero_mul, Nat.zero_add, emitLoop] using
      (ExecWithin.loop_exit (by simp [Cond.holds_lt, hz, hl]) :
        ExecWithin W (.loop (.lt zero link) emitBody) x x 2)
  | cons r rs ih =>
    obtain ⟨s, u⟩ := r
    cases hlinked with
    | cons hp hboundary hs hu htail =>
      have hsLt : s < 2 ^ m := hstates (s, u) List.mem_cons_self
      have ha1 : Fits W (ptr + 1) := hfit.of_le (by omega)
      have ha2 : Fits W (ptr + 2) := hfit.of_le (by omega)
      let loaded := x.set address (ptr + 1) |>.set state s |>.set address (ptr + 2)
        |>.set firstOperators u |>.set link (x.mem ptr)
      have heLoad : ExecWithin (B := .standard) W
          (ram[ address ← link + one; state ← *address; address ← address + one;
            firstOperators ← *address; link ← *link ]) x loaded 5 := by
        ram_eval [loaded, hl, hone, hs, hu, ha1, ha2, address, link, one, state,
          firstOperators, Fin.mk.injEq, Nat.add_assoc]
      obtain ⟨z, heEval, zs, _, _, zm, zone, _⟩ := evaluate_exec as (BitVec.ofNatLT s hsLt) loaded
        (v := v)
        (by simpa +decide [loaded, base, address, state, firstOperators, link] using hb)
        (by simpa +decide [loaded, count, address, state, firstOperators, link] using hc)
        (by simpa +decide [loaded, modulus, address, state, firstOperators, link] using hn)
        (by simp +decide [loaded, state, address, firstOperators, link])
        (by simpa +decide [loaded, operators, address, state, firstOperators, link] using hv) hfv
        hinput (hfit.of_le (by omega))
      have frame (r : Fin 32) (hr : evaluate.Preserves r) : z.regs r = loaded.regs r :=
        heEval.regs_eq hr
      have zo : z.regs output = o := by
        rw [frame output (by decide)]
        simpa +decide [loaded, output, address, state, firstOperators, link] using ho
      have zu : z.regs firstOperators = u := by
        rw [frame firstOperators (by decide)]
        simp +decide [loaded, firstOperators, link]
      have zv : z.regs operators = v := by
        rw [frame operators (by decide)]
        simpa +decide [loaded, operators, address, state, firstOperators, link] using hv
      let result := eval ((decode as.length v).zip as) (BitVec.ofNat m s)
      have zr : z.regs state = result.toNat := by
        simpa only [result, BitVec.ofNatLT_eq_ofNat] using zs
      let next := z.write o result.toNat |>.set output (o + 1)
        |>.write (o + 1) u |>.set output (o + 2)
        |>.write (o + 2) v |>.set output (o + 3)
      have heOut : ExecWithin (B := .standard) W
          (ram[ *output ← state; output ← output + one; *output ← firstOperators;
            output ← output + one; *output ← operators; output ← output + one ]) z next 6 := by
        have h1 : Fits W (o + 1) := hfit.of_le (by omega)
        have h2 : Fits W (o + 2) := hfit.of_le (by omega)
        have h3 : Fits W (o + 3) := hfit.of_le (by omega)
        ram_eval [next, zo, zr, zu, zv, zone, h1, h2, h3, output, state, one,
          firstOperators, operators, Nat.add_assoc, Fin.mk.injEq]
      have heBody : ExecWithin W emitBody x next (11 * as.length + 18) := by
        exact (heLoad.seq (heEval.seq heOut)).mono (by omega)
      have nmem : next.mem = emitMemory x.mem o result.toNat u v := by
        simp only [next, Data.set_mem, Data.write_mem, zm, loaded, emitMemory]
      have memoryFrame (a : ℕ) (ha : a < boundary) : next.mem a = x.mem a := by
        rw [nmem, emitMemory_outside]
        omega
      have nlinked : Linked next.mem boundary (x.mem ptr) rs := htail.frame memoryFrame
      have ninput : ∀ i (hi : i < as.length), next.mem (b + i) = as[i].toNat := by
        intro i hi
        rw [memoryFrame _ (by omega)]
        exact hinput i hi
      obtain ⟨y, heTail, ym, yo, yl⟩ := ih next
        (ptr := x.mem ptr) (o := o + 3)
        ((heBody.regs_eq (by decide)).trans hb)
        ((heBody.regs_eq (by decide)).trans hc)
        ((heBody.regs_eq (by decide)).trans hn)
        ((heBody.regs_eq (by decide)).trans hv)
        (by simp +decide [next, loaded, frame link (by decide), link, output])
        (by simp [next])
        (by simpa +decide [next, one, output] using zone)
        ((heBody.regs_eq (by decide)).trans hz) nlinked (by omega) ninput
        (by intro r hr; exact hstates r (List.mem_cons_of_mem _ hr))
        (hfit.of_le (by simp only [List.length_cons]; omega))
      refine ⟨y, ?_, ?_, ?_, yl⟩
      · exact (ExecWithin.loop_iter (by simp only [Cond.holds_lt, hz, hl]; exact hp)
          heBody heTail).mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
      · rw [emittedMemory, ← nmem]
        exact ym
      · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yo

/-- No record store escapes the output interval, even after later records have
been emitted. This is a final-state frame, not a global peak-space certificate. -/
theorem emittedMemory_outside {m : ℕ} (as : List (BitVec m)) (v : ℕ)
    (rs : List (ℕ × ℕ)) (mem : ℕ → ℕ) (o a : ℕ)
    (ha : ¬(o ≤ a ∧ a < o + 3 * rs.length)) : emittedMemory as v rs mem o a = mem a := by
  induction rs generalizing mem o with
  | nil => rfl
  | cons r rs ih =>
    rw [emittedMemory, ih]
    · exact emitMemory_outside _ _ _ _ _ _ (by simp only [List.length_cons] at ha; omega)
    · simp only [List.length_cons] at ha
      omega

/-- Each output cell is the full recovered state followed by its two quarter
indices. This specifies physical output, not merely an observer list. -/
theorem emittedMemory_read {m : ℕ} (as : List (BitVec m)) (v : ℕ)
    (rs : List (ℕ × ℕ)) (mem : ℕ → ℕ) (o j : ℕ) (hj : j < rs.length) :
    emittedMemory as v rs mem o (o + 3 * j) =
        (eval ((decode as.length v).zip as) (BitVec.ofNat m rs[j].1)).toNat ∧
    emittedMemory as v rs mem o (o + 3 * j + 1) = rs[j].2 ∧
    emittedMemory as v rs mem o (o + 3 * j + 2) = v := by
  induction rs generalizing mem o j with
  | nil => simp at hj
  | cons r rs ih =>
    obtain ⟨s, u⟩ := r
    cases j with
    | zero =>
      simp only [emittedMemory, Nat.mul_zero, Nat.add_zero]
      have frame (d : ℕ) (hd : d ≤ 2) :
          emittedMemory as v rs
              (emitMemory mem o (eval ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat u v)
              (o + 3) (o + d) =
            emitMemory mem o (eval ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat u v (o + d) :=
        emittedMemory_outside _ _ _ _ _ _ (by omega)
      have h0 := frame 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, frame 1 (by omega), frame 2 (by omega)]
      simp [emitMemory]
    | succ j =>
      have h := ih (emitMemory mem o
        (eval ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat u v) (o + 3) j (by
          simp only [List.length_cons] at hj; omega)
      simpa only [emittedMemory, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
