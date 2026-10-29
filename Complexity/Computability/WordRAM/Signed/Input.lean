/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Compile

/-!
# Complete signed-program translation with charged input preparation

The input words are encoded individually, using one unsigned word per source integer.
Both machines install their inputs without charging instructions. Their length headers differ:
the unsigned machine supplies the natural length, while the source representation needs its
signed encoding. A five-instruction prologue converts that header in place. The final native
halt returns the encoded signed output and is included in the simulation bound.

## Main definitions

* `ToWordRAM.prologue`, `ToWordRAM.compile`: input preparation and the complete fixed program.

## Main results

* `ToWordRAM.runs_compile_input`: run-prefix simulation preserving all memory and registers.
* `ToWordRAM.executes_compile_input`: every successful source execution transfers with two
  extra bits and at most `32 * t + 5` target instructions.

## References

The translation uses the existing signed RAM input convention and unsigned compiler.
-/

@[expose] public section

namespace Cslib.GenericRAM.Signed.ToWordRAM

open WordRAM (Code ExecWithin Exec)
open WordRAM.Signed
open scoped Cslib.WordRAM

variable {r : ℕ}

/-- Convert the native unsigned length header to its signed encoding in five instructions. -/
def prologue : Code .standard (r + 9) := ram[
  zero ← #0; two ← #2; left ← *zero; left ← left * two; *zero ← left ]

/-- The complete program, with a charged header conversion and fixed-size instruction blocks.
Callers supply `input.map encode` and decode the returned word, including for nonnegative values. -/
def compile (p : GenericRAM.Program model r) : WordRAM.Program .standard (r + 9) :=
  prologue.assemble 0 ++ compileFrom (prologue (r := r)).size 0 p

private def prepared (input : List ℤ) : WordRAM.Data (r + 9) :=
  let x := WordRAM.Data.init (input.map encode)
  ((((x.set zero 0).set two 2).set left input.length).set left (input.length * 2)).write 0
    (input.length * 2)

private theorem prepared_represents {w : ℕ} {input : List ℤ} (hi : Signed.InputFits w input) :
    Represents w (Signed.initial (r := r) input).data (prepared input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Signed.fits_zero hi.1.1
  · intro i
    have hzero : bank i ≠ zero := bank_ne_scratch i (by dsimp [zero]; omega)
    have htwo : bank i ≠ two := bank_ne_scratch i (by dsimp [two]; omega)
    have hleft : bank i ≠ left := bank_ne_scratch i (by dsimp [left]; omega)
    simp only [prepared, WordRAM.Data.write_regs, WordRAM.Data.set_regs,
      Function.update_of_ne hleft, Function.update_of_ne htwo, Function.update_of_ne hzero]
    rfl
  · intro a
    cases a with
    | zero =>
      simp [prepared, Signed.initial, GenericRAM.Data.init, encode, Nat.mul_comm]
    | succ a =>
      cases hv : input[a]? with
      | none =>
        simp [prepared, WordRAM.Data.init, Signed.initial, GenericRAM.Data.init,
          List.getD, List.getElem?_map, hv, encode]
      | some v =>
        simp [prepared, WordRAM.Data.init, Signed.initial, GenericRAM.Data.init,
          List.getD, List.getElem?_map, hv]

private theorem exec_prologue {w : ℕ} {input : List ℤ} (hi : Signed.InputFits w input) :
    Exec (w + 2) prologue (WordRAM.Data.init (input.map encode)) (prepared (r := r) input) 5 := by
  have h2 : WordRAM.Fits (w + 2) 2 :=
    (show WordRAM.Fits 2 2 from by decide).mono (by omega)
  have hlen : WordRAM.Fits (w + 2) (input.length * 2) := by
    have hf := (encode_fits (show Signed.Fits w (input.length : ℤ) from hi.1)).mono
      (by omega : w + 1 ≤ w + 2)
    have hn : ¬(input.length : ℤ) < 0 := by omega
    simpa [encode, Nat.mul_comm, hn] using hf
  ram_eval [prologue, prepared, WordRAM.Data.init, zero, two, left, Fin.mk.injEq,
    List.length_map, h2, hlen]

private theorem prepared_runs {w : ℕ} {input : List ℤ} (hi : Signed.InputFits w input)
    (p : GenericRAM.Program model r) :
    WordRAM.Runs (w + 2) (compile p) (WordRAM.State.init (input.map encode))
      ⟨5, prepared input⟩ 5 := by
  have hc : (compile p).Contains 0 (prologue.assemble 0) :=
    ⟨[], compileFrom (prologue (r := r)).size 0 p, by simp [compile], rfl⟩
  simpa [prologue, Code.size, WordRAM.State.init] using (exec_prologue hi).runs hc

/-- Complete run-prefix simulation preserves every source memory cell and register, with
charged header preparation and the translated instruction counter. This supports clients
whose observable output is a memory block rather than just the returned register. -/
theorem runs_compile_input {w n : ℕ} {p : GenericRAM.Program model r}
    {input : List ℤ} (hi : Signed.InputFits w input)
    {t : GenericRAM.State model r} (hr : GenericRAM.Runs w p (Signed.initial input) t n) :
    ∃ y k, k ≤ 32 * n + 5 ∧ WordRAM.Runs (w + 2) (compile p)
      (WordRAM.State.init (input.map encode)) ⟨entry 5 t.pc, y⟩ k ∧ Represents w t.data y := by
  obtain ⟨y, k, hk, he, hyr⟩ := runs_compile (prologue.assemble 0) (prepared_represents hi) hr
  have htail : WordRAM.Runs (w + 2) (compile p) ⟨5, prepared input⟩ ⟨entry 5 t.pc, y⟩ k := by
    simpa [compile, prologue, Code.size, entry, Signed.initial] using he
  exact ⟨y, 5 + k, by omega, (prepared_runs hi p).trans htail, hyr⟩

/-- The encoded source input fits the target width, including its native length header. -/
theorem inputFits_encode {w : ℕ} {input : List ℤ} (hi : Signed.InputFits w input) :
    WordRAM.InputFits (w + 2) (input.map encode) := by
  refine ⟨?_, ?_⟩
  · have hf := (encode_fits (show Signed.Fits w (input.length : ℤ) from hi.1)).mono
      (by omega : w + 1 ≤ w + 2)
    simpa only [List.length_map] using hf.of_le
      (show input.length ≤ encode (input.length : ℤ) by
        simp only [encode, Int.natAbs_natCast]
        split_ifs <;> omega)
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    exact (encode_fits (hi.2 z hz)).mono (by omega)

/-- Complete execution, starting from the ordinary unsigned input convention, costs at most
`32 * t + 5` instructions at width `w + 2` and returns the encoded signed output. Forward
correctness transfers successful runs without claiming reflection of source faults. -/
theorem executes_compile_input {w n : ℕ} {p : GenericRAM.Program model r}
    {input : List ℤ} (hi : Signed.InputFits w input) {v : ℤ}
    (hr : GenericRAM.Executes w p (Signed.initial input) v n) :
    ∃ k ≤ 32 * n + 5, WordRAM.Executes (w + 2) (compile p)
      (WordRAM.State.init (input.map encode)) (encode v) k := by
  obtain ⟨k, hk, he⟩ := executes_compile (prologue.assemble 0) (prepared_represents hi) hr
  have htail : WordRAM.Executes (w + 2) (compile p) ⟨5, prepared input⟩ (encode v) k := by
    simpa [compile, prologue, Code.size, entry, Signed.initial] using he
  refine ⟨5 + k, by omega, ?_⟩
  exact WordRAM.Executes.of_runs (prepared_runs hi p) htail

end Cslib.GenericRAM.Signed.ToWordRAM
