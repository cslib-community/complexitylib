/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.AKS.Congruence

/-!
# Powers and the AKS congruence on the word RAM

Concrete runs of repeated squaring modulo `X^r - 1` and `n` and of the congruence test, and
instances of their correctness theorems, including a congruence refuted by running the program.
-/

namespace ComplexityTests.WordRAMAKSCongruence

open Cslib.WordRAM Cslib.Algorithms.WordRAM

/-! ## Repeated squaring -/

/-- `R = 1` at `0`, `B = X + 1` at `2`, scratch at `4`, with `r = 2`, `n = 3` and exponent `e`. -/
private def powInput (e : ℕ) : Data 21 :=
  ⟨fun j => if j = AKS.PolyPow.B then 2 else if j = AKS.PolyPow.T then 4 else
      if j = AKS.PolyPow.rr then 2 else if j = AKS.PolyPow.nn then 3 else
      if j = AKS.PolyPow.e then e else 0,
    fun a => if a = 0 ∨ a = 2 ∨ a = 3 then 1 else if a < 4 then 0 else 5⟩

/-- `(X + 1)^2 = X² + 2X + 1 ≡ 2X + 2` modulo `X² - 1` and `3`. -/
example : (Code.eval 16 4 AKS.PolyPow.program (powInput 2)).map
      (fun yn => [yn.1.mem 0, yn.1.mem 1]) = some [2, 2] := by
  decide +kernel

/-- The correctness theorem at the same input: the result block is reduced modulo `7`. -/
example : ∃ y, ExecWithin 16 AKS.PolyPow.program (powInput 5) y (AKS.PolyPow.time 2 5) ∧
    ∀ i < 2, y.mem i < 3 := by
  obtain ⟨y, hy, -, hred, -⟩ := AKS.PolyPow.exec (w := 16) (powInput 5) (a := 0) (b := 2) (t := 4)
    (r := 2) (n := 3) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  exact ⟨y, hy, fun i hi => by simpa using hred i hi⟩

/-! ## The congruence test -/

/-- Blocks at `0`, `r` and `2r`, with `r`, `n` and `a` in their registers, over dirty memory. -/
private def congInput (r n a : ℕ) : Data 25 :=
  ⟨fun j => if j = AKS.Congruence.B then r else if j = AKS.Congruence.T then 2 * r else
      if j = AKS.Congruence.rr then r else if j = AKS.Congruence.nn then n else
      if j = AKS.Congruence.av then a else 0,
    fun _ => 3⟩

/-- `(X + 1)^3 ≡ X^3 + 1` modulo `X - 1` and `3`: both sides evaluate to `2` at `X = 1`. -/
example : (Code.eval 16 4 AKS.Congruence.program (congInput 1 3 1)).map
      (·.1.regs AKS.Congruence.flag) = some 1 := by
  decide +kernel

/-- The correctness theorem and a run refute `(X + 1)^4 ≡ X^4 + 1 (mod X - 1, 4)`: at `X = 1`
the sides are `16 ≡ 0` and `2`. -/
example : ¬ Cslib.AKS.Congruence 4 1 1 := by
  obtain ⟨y, ⟨m, -, hy⟩, -, hiff, -⟩ := AKS.Congruence.exec (w := 16) (congInput 1 4 1)
    (a := 0) (b := 1) (t := 2) (r := 1) (n := 4) (A := 1) rfl rfl rfl rfl rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hrun : (Code.eval 16 4 AKS.Congruence.program (congInput 1 4 1)).map
      (·.1.regs AKS.Congruence.flag) = some 0 := by decide +kernel
  obtain ⟨⟨y', k⟩, heval, hflag⟩ := Option.map_eq_some_iff.mp hrun
  obtain ⟨rfl, -⟩ := Exec.unique hy (Exec.of_eval heval)
  rw [← hiff, hflag]
  decide

end ComplexityTests.WordRAMAKSCongruence
