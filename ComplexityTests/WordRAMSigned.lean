/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Signed arithmetic regressions

Run the assembled unsigned programs, including their halting instruction. Exercise both signed
endpoints, cancellation, negative results, multiplication by zero, Euclidean division and
remainder across all sign combinations, total zero-divisor conventions, one-bit signed words and
overflow exclusions (including minimum/`-1` division). A caller with unrelated registers and
memory checks the preservation API.
-/

namespace ComplexityTests.WordRAMSigned

open Cslib.WordRAM
open Cslib.WordRAM.Signed

private def inputs (a b : ℤ) : Data 10 :=
  ⟨fun i => if i.val = 0 then encode a else if i.val = 1 then encode b else 0,
    fun _ => 0⟩

private def caller : Data 10 :=
  ⟨fun i => if i.val = 0 then encode (-8) else if i.val = 1 then encode 7 else 37,
    fun i => i % 17⟩

private def answer (c : Code .standard 10) (w : ℕ) (a b : ℤ) : Option ℕ :=
  (run w (c.program result) 32 ⟨0, inputs a b⟩).map Prod.fst

/-- Encoding, fit bounds, addition, subtraction, multiplication, one-bit words, and overflow. -/
example :
    (decode (encode (-8)) = -8 ∧ encode (-8) = 17 ∧
      Cslib.GenericRAM.Signed.Fits 4 (-8) ∧ Cslib.GenericRAM.Signed.Fits 4 7 ∧
      ¬Cslib.GenericRAM.Signed.Fits 4 8 ∧ ¬Cslib.GenericRAM.Signed.Fits 4 (-9)) ∧
    (answer add 6 (-8) 7 = some (encode (-1)) ∧
      answer add 6 7 (-8) = some (encode (-1)) ∧
      answer add 6 (-3) (-5) = some (encode (-8)) ∧
      answer add 6 3 4 = some (encode 7) ∧
      answer add 6 (-7) 7 = some (encode 0)) ∧
    (answer add 6 (-8) (-8) = some (encode (-16)) ∧
      answer subtract 6 7 (-8) = some (encode 15) ∧
      answer subtract 6 (-8) 7 = some (encode (-15)) ∧
      answer subtract 6 (-8) (-8) = some (encode 0) ∧
      answer subtract 6 (-3) 0 = some (encode (-3))) ∧
    (answer multiply 6 (-8) 1 = some (encode (-8)) ∧
      answer multiply 6 (-2) (-3) = some (encode 6) ∧
      answer multiply 6 2 (-3) = some (encode (-6)) ∧
      answer multiply 6 (-8) 0 = some (encode 0) ∧
      answer multiply 6 0 (-8) = some (encode 0)) ∧
    (Cslib.GenericRAM.Signed.Fits 1 (-1) ∧ Cslib.GenericRAM.Signed.Fits 1 0 ∧
      answer add 3 (-1) (-1) = some (encode (-2)) ∧
      answer subtract 3 0 (-1) = some (encode 1) ∧
      answer multiply 3 (-1) 0 = some (encode 0)) ∧
    -- Multiplication's result-fit premise excludes signed overflow. These routines do not
    -- promise to reproduce source faults: negating the minimum may succeed, while a larger
    -- product faults.
    (¬Cslib.GenericRAM.Signed.Fits 4 ((-8 : ℤ) * -1) ∧
      answer multiply 6 (-8) (-1) = some (encode 8) ∧
      answer multiply 6 (-8) (-8) = none) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- All three contracts hold on concrete bounded caller states, with an unrelated register
and nonzero memory. The output's encoding determines the mathematical integer. -/
example : caller.Bounded 6 := by
  constructor
  · intro i
    simp only [caller, Fits]
    split_ifs <;> decide
  · intro i
    exact lt_of_lt_of_le (Nat.mod_lt i (by decide : 0 < 17)) (by decide : 17 ≤ 2 ^ 6)

example : ∃ y, ExecWithin 6 add caller y 15 ∧
    decode (y.regs result) = -1 ∧ y.regs (9 : Fin 10) = 37 ∧
    y.regs left = encode (-8) ∧ y.mem 11 = 11 := by
  obtain ⟨y, hy, hv, hf⟩ := exec_add (w := 4) (a := -8) (b := 7)
    (by decide) (by decide) caller (by rfl) (by rfl)
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩
  · simpa only [hv, Cslib.GenericRAM.Signed.Arithmetic.eval, decode_encode] using
      (show (-8 : ℤ) + 7 = -1 by decide)
  · rw [hf.2 9 (by decide)]
    rfl
  · rw [hf.2 left (by decide)]
    rfl
  · rw [hf.1]
    rfl

/-- The public subtraction contract gives a flat halting program, charging its final halt. -/
example : ∃ n ≤ 18, Executes 6 ((subtract (r := 1)).program result)
    ⟨0, inputs (-8) 7⟩ (encode (-15)) n := by
  obtain ⟨y, ⟨n, hn, he⟩, hv, _⟩ := exec_subtract (w := 4) (a := -8) (b := 7)
    (by decide) (by decide) (inputs (-8) 7) (by rfl) (by rfl)
  exact ⟨n + 1, by omega, hv ▸ he.executes result⟩

/-- The multiplication contract also compiles, including the asymmetric negative endpoint. -/
example : ∃ n ≤ 15, Executes 6 ((multiply (r := 1)).program result)
    ⟨0, inputs (-8) 1⟩ (encode (-8)) n := by
  obtain ⟨y, ⟨n, hn, he⟩, hv, _⟩ := exec_multiply (w := 4) (a := -8) (b := 1)
    (by decide) (by decide) (by decide) (inputs (-8) 1) (by rfl) (by rfl)
  exact ⟨n + 1, by omega, hv ▸ he.executes result⟩

/-- Euclidean division and remainder across all four sign combinations, exact multiples,
zero-divisor conventions, asymmetric negative endpoint `-8` at `w = 4`, minimum/`-1` overflow,
and one-bit signed words (`w = 1`). -/
example :
    (answer divide 6 7 3 = some (encode 2) ∧
      answer modulo 6 7 3 = some (encode 1) ∧
      answer divide 6 7 (-3) = some (encode (-2)) ∧
      answer modulo 6 7 (-3) = some (encode 1) ∧
      answer divide 6 (-7) 3 = some (encode (-3)) ∧
      answer modulo 6 (-7) 3 = some (encode 2) ∧
      answer divide 6 (-7) (-3) = some (encode 3) ∧
      answer modulo 6 (-7) (-3) = some (encode 2)) ∧
    (answer divide 6 6 3 = some (encode 2) ∧
      answer modulo 6 6 3 = some (encode 0) ∧
      answer divide 6 6 (-3) = some (encode (-2)) ∧
      answer modulo 6 6 (-3) = some (encode 0) ∧
      answer divide 6 (-6) 3 = some (encode (-2)) ∧
      answer modulo 6 (-6) 3 = some (encode 0) ∧
      answer divide 6 (-6) (-3) = some (encode 2) ∧
      answer modulo 6 (-6) (-3) = some (encode 0) ∧
      answer divide 6 0 (-3) = some (encode 0) ∧
      answer modulo 6 0 (-3) = some (encode 0)) ∧
    (answer divide 6 7 0 = some (encode 0) ∧
      answer divide 6 (-8) 0 = some (encode 0) ∧
      answer divide 6 0 0 = some (encode 0) ∧
      answer modulo 6 7 0 = some (encode 7) ∧
      answer modulo 6 (-8) 0 = some (encode (-8)) ∧
      answer modulo 6 0 0 = some (encode 0)) ∧
    (answer divide 6 (-8) 3 = some (encode (-3)) ∧
      answer modulo 6 (-8) 3 = some (encode 1) ∧
      answer divide 6 (-8) (-3) = some (encode 3) ∧
      answer modulo 6 (-8) (-3) = some (encode 1) ∧
      answer divide 6 (-7) (-8) = some (encode 1) ∧
      answer modulo 6 (-7) (-8) = some (encode 1) ∧
      ¬Cslib.GenericRAM.Signed.Fits 4 ((-8 : ℤ) / -1) ∧
      Cslib.GenericRAM.Signed.Fits 4 ((-8 : ℤ) % -1) ∧
      answer divide 6 (-8) (-1) = some (encode 8) ∧
      answer modulo 6 (-8) (-1) = some (encode 0) ∧
      answer divide 3 (-1) (-1) = some (encode 1) ∧
      answer divide 3 (-1) 0 = some (encode 0) ∧
      answer modulo 3 (-1) (-1) = some (encode 0) ∧
      answer modulo 3 (-1) 0 = some (encode (-1))) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Division and remainder preserve the caller frame and obey their halting instruction bounds. -/
example : ∃ y, ExecWithin 6 divide caller y 20 ∧
    decode (y.regs result) = -2 ∧ y.regs (9 : Fin 10) = 37 ∧
    y.regs left = encode (-8) ∧ y.mem 11 = 11 := by
  obtain ⟨y, hy, hv, hf⟩ := exec_divide (w := 4) (a := -8) (b := 7)
    (by decide) (by decide) caller (by rfl) (by rfl)
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩
  · simpa only [hv, Cslib.GenericRAM.Signed.Arithmetic.eval, decode_encode] using
      (show (-8 : ℤ) / 7 = -2 by decide)
  · rw [hf.2 9 (by decide)]
    rfl
  · rw [hf.2 left (by decide)]
    rfl
  · rw [hf.1]
    rfl

example : ∃ n ≤ 14, Executes 6 ((modulo (r := 1)).program result)
    ⟨0, inputs (-8) 7⟩ (encode 6) n := by
  obtain ⟨y, ⟨n, hn, he⟩, hv, _⟩ := exec_modulo (w := 4) (a := -8) (b := 7)
    (by decide) (by decide) (inputs (-8) 7) (by rfl) (by rfl)
  exact ⟨n + 1, by omega, hv ▸ he.executes result⟩

end ComplexityTests.WordRAMSigned
